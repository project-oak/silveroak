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

From Coq Require Import Arith Eqdep_dec Vector Lia NArith Omega String Ndigits.
From Arrow Require Import Category Arrow.
From Cava Require Import Arrow.ArrowExport BitArithmetic.

From ArrowExamples Require Import Combinators Aes.pkg Aes.mix_columns Aes.sbox Aes.sub_bytes Aes.shift_rows.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

Definition cipher_round
  (sbox_impl: SboxImpl)
  : << Bit                               (* cipher mode: CIPH_FWD/CIPH_INV *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* data input *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* round key *)
    , Unit>> ~>
      Vector (Vector (Vector Bit 8) 4) 4 :=
  <[\op_i data_i key =>
    let stage1 = !(aes_sub_bytes sbox_impl) op_i data_i in
    let stage2 = !aes_shift_rows op_i stage1 in
    let stage3 = !aes_mix_columns op_i stage2 in
    stage3 ^ key
    ]>.

Definition final_cipher_round
  (sbox_impl: SboxImpl)
  : << Bit                               (* cipher mode: CIPH_FWD/CIPH_INV *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* data input *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* round key *)
    , Unit>> ~>
      Vector (Vector (Vector Bit 8) 4) 4 :=
  <[\op_i data_i key =>
    let stage1 = !(aes_sub_bytes sbox_impl) op_i data_i in
    let stage2 = !aes_shift_rows op_i stage1 in
    stage2 ^ key
    ]>.