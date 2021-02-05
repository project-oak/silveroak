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
  Context {signal} {semantics : Cava signal} {monad: Monad cava}.
  Context {round_index round_constant : SignalType}.

  Context (sub_bytes:     signal Bit -> signal state -> cava (signal state))
          (shift_rows:    signal Bit -> signal state -> cava (signal state))
          (mix_columns:   signal Bit -> signal state -> cava (signal state))
          (add_round_key: signal key -> signal state -> cava (signal state))
          (inv_mix_columns_key : signal key -> cava (signal key)).
  Context (key_expand : signal Bit -> signal round_index ->
                        (signal key  * signal round_constant) ->
                        cava (signal key * signal round_constant)).
  Context (num_rounds_regular : signal (round_index))
          (round_0 : signal (round_index)).
  Local Infix "==?" := eqb (at level 40).

  Definition cipher_round
             (is_decrypt : signal Bit) (input: signal state) (key : signal key)
    : cava (signal state) :=
    (sub_bytes is_decrypt   >=>
     shift_rows is_decrypt  >=>
     mix_columns is_decrypt >=>
     add_round_key key) input.

  Definition key_expand_and_round
             (is_decrypt : signal Bit)
             (key_rcon_input : signal key * signal round_constant * signal state)
             (add_round_key_in_sel : signal (Vec Bit 2))
             (round_key_sel : signal Bit)
             (round_i : signal round_index)
    : cava (signal key * signal round_constant * signal state) :=
    let '(round_key, rcon, input) := key_rcon_input in
    shift_rows_out <- (sub_bytes is_decrypt >=> shift_rows is_decrypt) input ;;
    mix_columns_out <- mix_columns is_decrypt shift_rows_out ;;

    (* Different rounds perform different operations on the state before adding
       the round key; select the appropriate wire based on add_round_key_in_sel *)
    let add_round_key_in :=
        mux4 (mkpair (mkpair (mkpair mix_columns_out input) shift_rows_out) mix_columns_out)
             add_round_key_in_sel in

    (* Intermediate decryption rounds need to mix the key columns *)
    mixed_round_key <- inv_mix_columns_key round_key ;;

    out <- add_round_key (pairSel round_key_sel (mkpair round_key mixed_round_key))
                        add_round_key_in ;;

    (* Key expansion *)
    '(round_key, rcon) <- key_expand is_decrypt round_i (round_key, rcon) ;;

    ret (round_key, rcon, out).

  Definition cipher_step
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (key_rcon_data : signal key * signal round_constant * signal state)
             (round_i : signal round_index)
    : cava (signal key * signal round_constant * signal state) :=
    let '(round_key, rcon, input) := key_rcon_data in
    is_first_round <- round_i ==? round_0 ;;
    is_final_round <- round_i ==? num_rounds_regular ;;
    (* add_round_key_in_sel :
       1 if round_i = 0, 2 if round_i = num_rounds_regular, 0 otherwise *)
    let add_round_key_in_sel := unpeel [is_first_round; is_final_round]%vector in
    is_middle_round <- nor2 (is_first_round, is_final_round) ;;
    (* round_key_sel : 1 for a decryption middle round, 0 otherwise *)
    round_key_sel <- and2 (is_middle_round, is_decrypt) ;;
    key_expand_and_round is_decrypt (round_key, rcon, input)
                         add_round_key_in_sel round_key_sel round_i.

  Definition cipher
             (is_decrypt : signal Bit) (* called op_i in OpenTitan *)
             (initial_key : signal key) (initial_rcon : signal round_constant)
             (round_indices : list (signal round_index)) (input : signal state)
    : cava (signal state) :=
    '(_, _, out) <- foldLM (cipher_step is_decrypt) round_indices
                          (initial_key, initial_rcon, input) ;;
    ret out.

End WithCava.
