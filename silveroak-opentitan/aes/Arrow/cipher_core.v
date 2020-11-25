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

From Coq Require Import NArith PeanoNat Strings.String Lists.List.
From Cava Require Import Arrow.ArrowExport BitArithmetic VectorUtils.

From Aes Require Import pkg mix_columns sbox sub_bytes shift_rows cipher_round key_expand aes_test.

Import ListNotations.
Import KappaNotation.
Open Scope kappa_scope.

Definition key_expand_and_round (sbox_impl: SboxImpl) :=
  <[ fun "key_expand_and_round"
    (op_i: _ Bit)
    (round: _ (Vector Bit 4))
    (data_i: _ (Vector (Vector (Vector Bit 8) 4) 4))
    (key: _ (Vector (Vector (Vector Bit 8) 4) 8))
    (step_i: _ Bit)
    (clear_i: _ Bit)
    : << Vector (Vector (Vector Bit 8) 4) 4 (* data *)
      ,  Vector (Vector (Vector Bit 8) 4) 8 (* key *)
      >> =>

    let key_words = !aes_transpose
      (if op_i == !CIPH_FWD
      then key[:7:4]
      else key[:3:0])
      in
    let round_key =
      if op_i == !CIPH_FWD
      then key_words
      else !aes_mix_columns !CIPH_INV key_words in

    let data_o =
      !(cipher_round_combined sbox_impl) op_i data_i round_key (round == #0) (round == #14) in

    let new_key = !(aes_key_expand sbox_impl) op_i step_i clear_i round key in
    (data_o, new_key)
  ]>.

Definition aes_cipher_core_mealy
  (sbox_impl: SboxImpl) :=
  <[ fun "aes_cipher_core_mealy" state input
    : <<
       (* state *)
       << Bit (* op_s *)
       , Vector (Vector (Vector Bit 8) 4) 4 (*data_s*)
       , Vector (Vector (Vector Bit 8) 4) 8 (*key_s *)
       , Vector Bit 4 (* next round *)
       >>,

       (* output *)
       << Bit (* valid output *)
       , Bit (* Accept data *)
       , Bit (* Accept key *)
       , Vector (Vector (Vector Bit 8) 4) 4 (*data_o*)
       >>
      >> =>

    let '(op_s, data_s, key_s, current_round) = state in
    let '(op_i, data_i, data_valid, key_i, key_valid, data_o_ready) = input in

    let step = false' in
    let clear = false' in

    let round_inc = current_round +% #1 in

    let done = (current_round == #14) || (current_round == #15) in
    let reset = (current_round == #15) && data_o_ready in

    let '(data_n, key_n) =
      if current_round == #15
      then (data_s, key_s)
      else !(key_expand_and_round sbox_impl)
        op_i current_round data_s key_s step clear in

    let next_round =
      if done then
        if reset then #0
        else #15
      else round_inc in

    ( ( op_s
      , if done && data_valid then data_i else data_n
      , if done && key_valid then key_i else key_n
      , next_round )
    , ( (current_round == #15)
      , done
      , done
      , data_i )
    )

  ]>.

(* TODO(#357): op_i needs valid flag and to be respected *)
Definition aes_cipher_core
  (sbox_impl: SboxImpl) :=
  <[ fun "aes_cipher_core"
    (op_i: _ Bit)
    (data_i: _ (Vector (Vector (Vector Bit 8) 4) 4))
    (data_valid: _ Bit)
    (key_i: _ (Vector (Vector (Vector Bit 8) 4) 8))
    (key_valid: _ Bit)
    (data_o_ready: _ Bit)

    : <<
         Bit (* valid output *)
       , Bit (* Accept data *)
       , Bit (* Accept key *)
       , Vector (Vector (Vector Bit 8) 4) 4 (*data_o*)
       >> =>

    !(mealy_machine (aes_cipher_core_mealy sbox_impl))
      (op_i, data_i, data_valid, key_i, key_valid, data_o_ready)
  ]>.

Definition test_input : list
  (bool *
    (denote_kind << Vector (Vector (Vector Bit 8) 4) 4 >> * (bool *
    (denote_kind << Vector (Vector (Vector Bit 8) 4) 8 >> * (bool * bool))))) :=
  [
    (false,
      (@reshape _ 4 4 (reshape test_data), (false,
      (@reshape _ 8 4 (reshape test_key), (false, false )))))
  ].

(* TODO(#357): evaluate *)
Eval vm_compute in
  (interp_sequential (((aes_cipher_core SboxLut) : Kappa _ _) _) test_input).

