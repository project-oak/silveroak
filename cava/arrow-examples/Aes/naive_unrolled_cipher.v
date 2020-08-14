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

Definition rcon_const
  : << Vector Bit 4, Unit >> ~> Vector (Vector Bit 8) 4 :=
  <[\idx =>
    (* let array = 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36 *)
    let array = #1 :: #2 :: #4 :: #8 :: #16 :: #32 :: #64 :: #128 :: #27 :: #48 :: [] in
    array[idx] :: #0 :: #0 :: #0 :: []
  ]>.

Definition key_expansion_word
  (sbox_impl: SboxImpl)
  (is_0_mod_8: bool)
  : << Vector (Vector Bit 8) 4
    ,  Vector (Vector (Vector Bit 8) 4) 4
    ,  Vector (Vector (Vector Bit 8) 4) 4
    ,  Unit>> ~>
       Vector (Vector (Vector Bit 8) 4) 4
    :=
  let sbox := map <[ !(aes_sbox sbox_impl) !CIPH_FWD ]> in
  let rot := if is_0_mod_8
    then <[\x => !aes_circ_byte_shift x #3 ]>
    else <[\x => x ]> in
  let apply_rcon := if is_0_mod_8
    then <[\x rcon => x ^ rcon ]>
    else <[\x rcon => x ]> in
  <[\rcon k0 k1 =>
    let '(_, word) = unsnoc k1 in
    let rot_word_out = !rot word in
    let sub_rot_word_out = !sbox rot_word_out in

    let w0 = k0[#0] ^ !apply_rcon sub_rot_word_out rcon in
    let w1 = k0[#1] ^ w0 in 
    let w2 = k0[#2] ^ w1 in 
    let w3 = k0[#3] ^ w2 in 

    w0 :: w1 :: w2 :: w3 :: []
  ]>.

Definition aes_256_naive_key_expansion
  (sbox_impl: SboxImpl)
  : << Vector (Vector (Vector Bit 8) 4) 4
    ,  Vector (Vector (Vector Bit 8) 4) 4
    ,  Unit>> ~>
    << Vector (Vector (Vector (Vector Bit 8) 4) 4) 15 >>
    :=
    let f := key_expansion_word sbox_impl true in
    let g := key_expansion_word sbox_impl false in
  <[\k0 k1 =>
    (* TODO(blaxill): add scan op *)
    let k2 = !f (!rcon_const #0) k0 k1 in
    (* TODO(blaxill): rcon unnecessary on g *)
    let k3 = !g (!rcon_const #0) k1 k2 in 

    let k4 = !f (!rcon_const #1) k2 k3 in
    let k5 = !g (!rcon_const #1) k3 k4 in
    let k6 = !f (!rcon_const #2) k4 k5 in
    let k7 = !g (!rcon_const #2) k5 k6 in
    let k8 = !f (!rcon_const #3) k6 k7 in
    let k9 = !g (!rcon_const #3) k7 k8 in
    let k10= !f (!rcon_const #4) k8 k9 in
    let k11= !g (!rcon_const #4) k9 k10 in
    let k12= !f (!rcon_const #5) k10 k11 in
    let k13= !g (!rcon_const #5) k11 k12 in
    let k14= !f (!rcon_const #6) k12 k13 in
    let k15= !g (!rcon_const #6) k13 k14 in

    k0 :: k1 ::
    k2 :: k3 ::
    k4 :: k5 ::
    k6 :: k7 ::
    k8 :: k9 ::
    k10:: k11::
    k12:: k13::
    k14:: []
  ]>.

Lemma key_expansion_comb: is_combinational (aes_256_naive_key_expansion SboxCanright).
Proof. simply_combinational. Qed.

Definition expanded_key := combinational_evaluation (aes_256_naive_key_expansion SboxCanright) key_expansion_comb (kind_default _).

Compute (Vector.map (Vector.map (Vector.map Bv2N)) expanded_key).

(* AES-256 expanded empty key *)
(* 
0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00 = k0
0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00, ~ 0x00, 0x00, 0x00, 0x00 = k1
0x62, 0x63, 0x63, 0x63, ~ 0x62, 0x63, 0x63, 0x63, ~ 0x62, 0x63, 0x63, 0x63, ~ 0x62, 0x63, 0x63, 0x63 = k2
0xaa, 0xfb, 0xfb, 0xfb, ~ 0xaa, 0xfb, 0xfb, 0xfb, ~ 0xaa, 0xfb, 0xfb, 0xfb, ~ 0xaa, 0xfb, 0xfb, 0xfb = k3
0x6f, 0x6c, 0x6c, 0xcf, ~ 0x0d, 0x0f, 0x0f, 0xac, ~ 0x6f, 0x6c, 0x6c, 0xcf, ~ 0x0d, 0x0f, 0x0f, 0xac = k4
0x7d, 0x8d, 0x8d, 0x6a, ~ 0xd7, 0x76, 0x76, 0x91, ~ 0x7d, 0x8d, 0x8d, 0x6a, ~ 0xd7, 0x76, 0x76, 0x91 = k5
0x53, 0x54, 0xed, 0xc1, ~ 0x5e, 0x5b, 0xe2, 0x6d, ~ 0x31, 0x37, 0x8e, 0xa2, ~ 0x3c, 0x38, 0x81, 0x0e = k6
0x96, 0x8a, 0x81, 0xc1, ~ 0x41, 0xfc, 0xf7, 0x50, ~ 0x3c, 0x71, 0x7a, 0x3a, ~ 0xeb, 0x07, 0x0c, 0xab = k7
0x9e, 0xaa, 0x8f, 0x28, ~ 0xc0, 0xf1, 0x6d, 0x45, ~ 0xf1, 0xc6, 0xe3, 0xe7, ~ 0xcd, 0xfe, 0x62, 0xe9 = k8
0x2b, 0x31, 0x2b, 0xdf, ~ 0x6a, 0xcd, 0xdc, 0x8f, ~ 0x56, 0xbc, 0xa6, 0xb5, ~ 0xbd, 0xbb, 0xaa, 0x1e = k9
0x64, 0x06, 0xfd, 0x52, ~ 0xa4, 0xf7, 0x90, 0x17, ~ 0x55, 0x31, 0x73, 0xf0, ~ 0x98, 0xcf, 0x11, 0x19 = k10
0x6d, 0xbb, 0xa9, 0x0b, ~ 0x07, 0x76, 0x75, 0x84, ~ 0x51, 0xca, 0xd3, 0x31, ~ 0xec, 0x71, 0x79, 0x2f = k11
0xe7, 0xb0, 0xe8, 0x9c, ~ 0x43, 0x47, 0x78, 0x8b, ~ 0x16, 0x76, 0x0b, 0x7b, ~ 0x8e, 0xb9, 0x1a, 0x62 = k12
0x74, 0xed, 0x0b, 0xa1, ~ 0x73, 0x9b, 0x7e, 0x25, ~ 0x22, 0x51, 0xad, 0x14, ~ 0xce, 0x20, 0xd4, 0x3b = k13
0x10, 0xf8, 0x0a, 0x17, ~ 0x53, 0xbf, 0x72, 0x9c, ~ 0x45, 0xc9, 0x79, 0xe7, ~ 0xcb, 0x70, 0x63, 0x85 = k14
*)