(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.CavaPrelude.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Combinators.

Local Open Scope monad_scope.

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {key round_constant state round_index : SignalType}.

  Context (sub_bytes:     signal Bit -> signal state -> cava (signal state))
          (shift_rows:    signal Bit -> signal state -> cava (signal state))
          (mix_columns:   signal Bit -> signal state -> cava (signal state))
          (add_round_key: signal key -> signal state -> cava (signal state))
          (inv_mix_columns_key : signal key -> cava (signal key)).
  Context (key_expand : signal Bit -> signal round_index ->
                        (signal key  * signal round_constant) ->
                        cava (signal key * signal round_constant)).
  Local Infix "==?" := eqb (at level 40).

  (* State of the AES cipher (key, round constant, AES state vector) *)
  Let cipher_state : Type := signal key * signal round_constant * signal state.
  (* The non-state signals that each round of the cipher loop needs access to *)
  Let cipher_signals : Type :=
    signal Bit (* op_i/is_decrypt : true for decryption, false for encryption *)
      * signal round_index (* num_rounds_regular : round index of final round *)
      * signal round_index (* round_0 : round index of first round *)
      * cipher_state (* initial state, ignored for all rounds except first *)
      * signal round_index (* current round_index *).

  Definition key_expand_and_round
             (is_decrypt : signal Bit)
             (key_rcon_data : cipher_state)
             (add_round_key_in_sel : signal (Vec Bit 2))
             (round_key_sel : signal Bit)
             (round_i : signal round_index)
    : cava (cipher_state) :=
    let '(round_key, rcon, data) := key_rcon_data in
    shift_rows_out <- (sub_bytes is_decrypt >=> shift_rows is_decrypt) data ;;
    mix_columns_out <- mix_columns is_decrypt shift_rows_out ;;

    (* Different rounds perform different operations on the state before adding
       the round key; select the appropriate wire based on add_round_key_in_sel *)
    let add_round_key_in :=
        mux4Tuple (mix_columns_out, data, shift_rows_out, mix_columns_out)
                  add_round_key_in_sel in

    (* Intermediate decryption rounds need to mix the key columns *)
    mixed_round_key <- inv_mix_columns_key round_key ;;

    key_to_add <- muxPair round_key_sel (round_key, mixed_round_key) ;;
    out <- add_round_key key_to_add add_round_key_in ;;

    (* Key expansion *)
    '(round_key, rcon) <- key_expand is_decrypt round_i (round_key, rcon) ;;

    ret (round_key, rcon, out).

  Definition cipher_step
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (is_first_round : signal Bit)
             (num_rounds_regular : signal round_index)
             (key_rcon_data : cipher_state)
             (round_i : signal round_index)
    : cava (cipher_state) :=
    let '(round_key, rcon, data) := key_rcon_data in
    is_final_round <- round_i ==? num_rounds_regular;;
    (* add_round_key_in_sel :
       1 if round_i = 0, 2 if round_i = num_rounds_regular, 0 otherwise *)
    let add_round_key_in_sel := unpeel [is_first_round; is_final_round]%vector in
    is_middle_round <- nor2 (is_first_round, is_final_round) ;;
    (* round_key_sel : 1 for a decryption middle round, 0 otherwise *)
    round_key_sel <- and2 (is_middle_round, is_decrypt) ;;
    key_expand_and_round is_decrypt key_rcon_data
                         add_round_key_in_sel round_key_sel round_i.

  Definition cipher_loop
    : Circuit cipher_signals cipher_state :=
    Loop
      (Loop
         (Loop
            (Comb
               (fun input_and_state :
                    cipher_signals * signal key * signal round_constant * signal state  =>
                  let '(input, fk, fr, fv) := input_and_state in
                  (* extract signals from the input tuple *)
                  let '(is_decrypt, num_rounds_regular,
                        round_0, initial_state, idx) := input in
                  let '(ik, ir, iv) := initial_state in
                  is_first_round <- idx ==? round_0 ;;
                  k <- muxPair is_first_round (fk, ik) ;;
                  r <- muxPair is_first_round (fr, ir) ;;
                  v <- muxPair is_first_round (fv, iv) ;;
                  '(k',r',v') <- cipher_step is_decrypt is_first_round
                                            num_rounds_regular (k,r,v) idx ;;
                  let out := (k',r',v') in
                  ret (out,k',r',v'))))).

  Definition cipher
    : Circuit cipher_signals (signal state) :=
    Compose cipher_loop
            (Comb (fun '(_,out) => ret out)).
End WithCava.
