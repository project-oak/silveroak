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
Import Circuit.Notations.

Local Open Scope monad_scope.

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {key state round_index : SignalType}.

  Context (sub_bytes:     signal Bit -> signal state -> cava (signal state))
          (shift_rows:    signal Bit -> signal state -> cava (signal state))
          (mix_columns:   signal Bit -> signal state -> cava (signal state))
          (add_round_key: signal key -> signal state -> cava (signal state))
          (inv_mix_columns_key : signal key -> cava (signal key)).
  Local Infix "==?" := eqb (at level 40).

  (* The non-state signals that each round of the cipher loop needs access to *)
  Let cipher_signals : Type :=
    signal Bit (* op_i/is_decrypt : true for decryption, false for encryption *)
      * signal round_index (* num_rounds_regular : round index of final round *)
      * signal round_index (* round_0 : round index of first round *)
      * signal round_index (* current round_index *)
      * signal key (* initial key, ignored for all rounds except first *)
      * signal state (* initial state, ignored for all rounds except first *).

  Definition cipher_round
             (is_decrypt : signal Bit)
             (round_key : signal key)
             (add_round_key_in_sel : signal (Vec Bit 2))
             (round_key_sel : signal Bit)
             (round_i : signal round_index)
             (data : signal state)
    : cava (signal state) :=
    shift_rows_out <- (sub_bytes is_decrypt >=> shift_rows is_decrypt) data ;;
    mix_columns_out <- mix_columns is_decrypt shift_rows_out ;;

    (* Different rounds perform different operations on the state before adding
       the round key; select the appropriate wire based on add_round_key_in_sel *)
    add_round_key_in <-
        mux4 (mix_columns_out, data, shift_rows_out, mix_columns_out)
             add_round_key_in_sel ;;

    (* Intermediate decryption rounds need to mix the key columns *)
    mixed_round_key <- inv_mix_columns_key round_key ;;

    key_to_add <- mux2 round_key_sel (round_key, mixed_round_key) ;;
    out <- add_round_key key_to_add add_round_key_in ;;

    ret out.

  Definition cipher_step
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (is_first_round : signal Bit)
             (num_rounds_regular : signal round_index)
             (round_key : signal key)
             (round_i : signal round_index)
             (data : signal state)
    : cava (signal state) :=
    is_final_round <- round_i ==? num_rounds_regular;;
    (* add_round_key_in_sel :
       1 if round_i = 0, 2 if round_i = num_rounds_regular, 0 otherwise *)
    add_round_key_in_sel <- unpeel [is_first_round; is_final_round]%vector ;;
    is_middle_round <- nor2 (is_first_round, is_final_round) ;;
    (* round_key_sel : 1 for a decryption middle round, 0 otherwise *)
    round_key_sel <- and2 (is_middle_round, is_decrypt) ;;
    cipher_round is_decrypt round_key
                 add_round_key_in_sel round_key_sel round_i data.

  Definition cipher_loop
    : Circuit (cipher_signals * signal key) (signal state) :=
    Loop
      (Comb
         (fun input_and_state :
              cipher_signals * signal key * signal state  =>
            let '(input, k, feedback_state) := input_and_state in
            (* extract signals from the input tuple *)
            let '(is_decrypt, num_rounds_regular,
                  round_0, idx, _, initial_state) := input in
            is_first_round <- idx ==? round_0 ;;
            st <- mux2 is_first_round (feedback_state, initial_state) ;;
            st' <- cipher_step is_decrypt is_first_round
                             num_rounds_regular k idx st ;;
            ret (st',st'))).

  Definition cipher
             (key_expand : Circuit cipher_signals (signal key))
    : Circuit cipher_signals (signal state) :=
    (Comb fork2)
      >==> Second key_expand
      >==> cipher_loop.
End WithCava.
