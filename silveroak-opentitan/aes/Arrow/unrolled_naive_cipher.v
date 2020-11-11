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

From Coq Require Import Arith.Arith Logic.Eqdep_dec Vectors.Vector micromega.Lia
     NArith.NArith Strings.String NArith.Ndigits.
From Cava Require Import BitArithmetic VectorUtils Arrow.ArrowExport.

From Aes Require Import pkg mix_columns sbox sub_bytes shift_rows cipher_round.
From Aes Require Import aes_test.

Require Import coqutil.Z.HexNotation.

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

Definition aes_256_naive_key_expansion'
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

Definition aes_256_naive_key_expansion
  (sbox_impl: SboxImpl)
  : << Vector (Vector (Vector Bit 8) 4) 8
    ,  Unit>> ~>
    << Vector (Vector (Vector (Vector Bit 8) 4) 4) 15 >>
    := <[\ key =>
    let '(key0, key1) = !(split_pow2 _ 2) key in
    !(aes_256_naive_key_expansion' sbox_impl) key0 key1
    ]>.

Definition unrolled_cipher_naive'
  (sbox_impl: SboxImpl)
  : <<
      Bit (* op *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* data *)
    , Vector (Vector (Vector Bit 8) 4) 8 (* key *)
    , Unit
    >> ~>
    <<
      Vector (Vector (Vector Bit 8) 4) 4 (* data *)
    >>
  :=
  let aes_key_expand := aes_256_naive_key_expansion sbox_impl in
  <[\op_i data_i key =>
    let keys = !aes_key_expand key in

    let '(first_key, keys_uncons) = uncons (if op_i == !CIPH_FWD then keys else !reverse keys) in
    let '(middle_keys, last_key) = unsnoc keys_uncons in

    let initial_rounds =
      !(foldl <[\ ctxt key =>
        let '(op_i, data_i) = ctxt in
          (op_i, !(cipher_round sbox_impl) op_i data_i key)
          ]>)
        (op_i, data_i ^ !aes_transpose first_key)
        (if op_i == !CIPH_FWD
        then !(map aes_transpose) middle_keys
        else !(map <[\x => !aes_mix_columns !CIPH_INV (!aes_transpose x)]>) middle_keys) in

    !(final_cipher_round sbox_impl) op_i (snd initial_rounds) (!aes_transpose last_key)
    ]>.

Definition unrolled_cipher_naive
  (sbox_impl: SboxImpl)
  : <<
      Bit
    , Vector Bit 128 (* data *)
    , Vector Bit 256 (* key *)
    , Unit
    >> ~>
    <<
     Vector Bit 128 (* data *)
    >>
  :=
  <[\op_i data key =>
    let data_o =
      !(unrolled_cipher_naive' sbox_impl) op_i
      (!aes_transpose (!reshape (!reshape data)))
      (!reshape (!reshape key)) in
    !flatten (!flatten (!aes_transpose data_o))
    ]>.

Section tests.

  Definition unrolled_cipher_naive_ mode key data :=
    kinterp (unrolled_cipher_naive SboxCanright) (mode,(data,(key, tt))).

  Definition naive_cipher_test_fwd := test_cipher_fwd unrolled_cipher_naive_.
  Definition naive_cipher_value_fwd := print_cipher_fwd unrolled_cipher_naive_.
  Definition naive_cipher_test_rev := test_cipher_rev unrolled_cipher_naive_.
  Definition naive_cipher_value_rev := print_cipher_rev unrolled_cipher_naive_.

End tests.

