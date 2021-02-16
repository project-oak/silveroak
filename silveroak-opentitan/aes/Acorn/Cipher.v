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

Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Combinators.
Require Import AcornAes.Pkg.
Import Pkg.Notations.

Local Open Scope monad_scope.

Section WithCava.
  Context {signal} {semantics : Cava signal} {seqsemantics : CavaSeq semantics}.
  Context {round_index round_constant : SignalType}.

  Context (sub_bytes:     signal Bit -> signal state -> cava (signal state))
          (shift_rows:    signal Bit -> signal state -> cava (signal state))
          (mix_columns:   signal Bit -> signal state -> cava (signal state))
          (add_round_key: signal key -> signal state -> cava (signal state))
          (inv_mix_columns_key : signal key -> cava (signal key)).
  Context (key_expand : signal Bit -> signal round_index ->
                        (signal key  * signal round_constant) ->
                        cava (signal key * signal round_constant)).
  Local Infix "==?" := eqb (at level 40).
  Local Infix "**" := Pair (at level 40, left associativity).

  (* State of the AES cipher (key, round constant, AES state vector) *)
  Let cipher_state : SignalType := key ** round_constant ** state.
  (* The non-state signals that each round of the cipher loop needs access to *)
  Let cipher_signals : SignalType :=
    Bit (* op_i/is_decrypt : true for decryption, false for encryption *)
      ** round_index (* num_rounds_regular : round index of final round *)
      ** round_index (* round_0 : round index of first round *)
      ** cipher_state (* initial state, ignored for all rounds except first *)
      ** round_index (* current round_index *).

  Definition key_expand_and_round
             (is_decrypt : signal Bit)
             (key_rcon_data : signal cipher_state)
             (add_round_key_in_sel : signal (Vec Bit 2))
             (round_key_sel : signal Bit)
             (round_i : signal round_index)
    : cava (signal cipher_state) :=
    let '(key_rcon, data) := unpair key_rcon_data in
    let '(round_key, rcon) := unpair key_rcon in
    shift_rows_out <- (sub_bytes is_decrypt >=> shift_rows is_decrypt) data ;;
    mix_columns_out <- mix_columns is_decrypt shift_rows_out ;;

    (* Different rounds perform different operations on the state before adding
       the round key; select the appropriate wire based on add_round_key_in_sel *)
    let add_round_key_in :=
        mux4 (mkpair (mkpair (mkpair mix_columns_out data) shift_rows_out) mix_columns_out)
             add_round_key_in_sel in

    (* Intermediate decryption rounds need to mix the key columns *)
    mixed_round_key <- inv_mix_columns_key round_key ;;

    key_to_add <- muxPair round_key_sel (round_key, mixed_round_key) ;;
    out <- add_round_key key_to_add add_round_key_in ;;

    (* Key expansion *)
    '(round_key, rcon) <- key_expand is_decrypt round_i (round_key, rcon) ;;

    ret (mkpair (mkpair round_key rcon) out).

  Definition cipher_step
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (is_first_round : signal Bit)
             (num_rounds_regular : signal round_index)
             (key_rcon_data : signal cipher_state)
             (round_i : signal round_index)
    : cava (signal cipher_state) :=
    let '(key_rcon, data) := unpair key_rcon_data in
    let '(round_key, rcon) := unpair key_rcon in
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
    : signal cipher_signals -> cava (signal cipher_state) :=
    loopDelayS
      (fun input_and_state : signal cipher_signals
                           * signal cipher_state =>
         let '(input, feedback_state) := input_and_state in
         (* extract signals from the input tuple *)
         let '(input, idx) := unpair input in
         let '(input, initial_state) := unpair input in
         let '(input, round_0) := unpair input in
         let '(is_decrypt, num_rounds_regular) := unpair input in

         is_first_round <- idx ==? round_0 ;;
         cipher_state <- muxPair is_first_round (feedback_state, initial_state) ;;
         cipher_step is_decrypt is_first_round num_rounds_regular
                     cipher_state idx).

  Definition cipher
             (initial_rcon_selector : signal Bit -> cava (signal round_constant))
             (num_rounds_regular round_0 : signal round_index)
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (initial_key : signal key) (initial_state : signal state)
             (round_i : signal round_index)
    : cava (signal state) :=
    initial_rcon <- initial_rcon_selector is_decrypt ;;
    (* combine all the input signals *)
    let initial_cipher_state : signal cipher_state :=
        mkpair (mkpair initial_key initial_rcon) initial_state in
    let loop_input : signal cipher_signals :=
        mkpair (mkpair (mkpair (mkpair is_decrypt num_rounds_regular)
                               round_0) initial_cipher_state) round_i in
    (* run the AES loop *)
    loop_out <- cipher_loop loop_input ;;
    (* select the AES state vector as output *)
    ret (snd (unpair loop_out)).
End WithCava.
