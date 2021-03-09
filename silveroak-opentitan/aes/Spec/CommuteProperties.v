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

Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Coq.Vectors.Vector.

Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.List.
Require Import Cava.Util.Vector.
Require Import AesSpec.AddRoundKey.
Require Import AesSpec.MixColumns.
Require Import AesSpec.ShiftRows.
Require Import AesSpec.SubBytes.
Require Import AesSpec.Sbox.
Require Import AesSpec.StateTypeConversions.

Section SubBytesShiftRows.
  Lemma sub_byte_shift_row_once_comm : forall row,
    shift_row_once (map forward_sbox row) =
    map forward_sbox (shift_row_once row).
  Proof.
    intros.
    destruct row; [reflexivity|].
    simpl.
    rewrite map_app.
    reflexivity.
  Qed.

  Lemma sub_byte_shift_row_comm : forall row shift,
      shift_row (map forward_sbox row) shift =
      map forward_sbox (shift_row row shift).
  Proof.
    intros.
    generalize dependent row.
    induction shift; [reflexivity|].
    intros.
    simpl.
    rewrite <- IHshift.
    rewrite sub_byte_shift_row_once_comm.
    reflexivity.
  Qed.

  Lemma sub_bytes_shift_rows_start_comm : forall st n,
      shift_rows_start (sub_bytes st) n =
      sub_bytes (shift_rows_start st n).
  Proof.
    induction st; [reflexivity|].
    intro n.
    unfold shift_rows_start.
    simpl.
    rewrite sub_byte_shift_row_comm.
    unfold shift_rows_start in IHst.
    rewrite IHst.
    reflexivity.
  Qed.

  Theorem sub_bytes_shift_rows_comm : forall st,
      shift_rows (sub_bytes st) = sub_bytes (shift_rows st).
  Proof.
    intros.
    apply (sub_bytes_shift_rows_start_comm st 0).
  Qed.
End SubBytesShiftRows.

Section MixColsAddRoundKey.
  Existing Instance byteops.
  Local Notation to_bits x := (LittleEndian.to_cols_bits (BigEndian.from_cols x)) (only parsing).
  Local Notation from_bits x := (BigEndian.to_cols (LittleEndian.from_cols_bits x)) (only parsing).


  Lemma poly_to_byte_to_bitvec b :
    length b = 8%nat ->
    byte_to_bitvec (poly_to_byte b) = of_list_sized false 8 b.
  Proof.
    intros. destruct_lists_by_length.
    cbv [byte_to_bitvec poly_to_byte].
    repeat match goal with b : bool |- _ => destruct b end;
      vm_compute; reflexivity.
  Qed.

  Lemma byte_add_is_xor b1 b2 :
    byte_to_bitvec (Polynomial.fadd b1 b2)
    = Vector.map2 xorb (byte_to_bitvec b1) (byte_to_bitvec b2).
  Proof.
    cbv [Polynomial.fadd byteops].
    rewrite poly_to_byte_to_bitvec by length_hammer.
    apply to_list_inj. autorewrite with push_to_list.
    rewrite to_list_of_list_sized by length_hammer.
    cbv [Polynomial.add_poly].
    rewrite !extend_le by length_hammer.
    reflexivity.
  Qed.

  Lemma add_round_key_byte_add (st k : Vector.t (Vector.t byte 4) 4) :
    add_round_key 32 4 (to_bits st) (to_bits k)
    = to_bits (Vector.map2 (Vector.map2 Polynomial.fadd) st k).
  Proof.
    cbv [add_round_key Bvector.BVxor].
    cbv [LittleEndian.to_cols_bits].
    autorewrite with conversions.
    rewrite map_map2, <-reverse_map2, map2_map.
    f_equal. apply map2_ext; intros.
    rewrite reverse_map2.
    cbv [bytevec_to_bitvec].
    rewrite map2_flatten with (m:=4) (n:=8).
    rewrite map_map2, map2_map. f_equal.
    apply map2_ext; intros.
    rewrite byte_add_is_xor; reflexivity.
  Qed.

  Lemma inv_mix_columns_add_round_key_comm (st k : Vector.t (Vector.t byte 4) 4) :
    add_round_key 32 4
                  (to_bits (inv_mix_columns st))
                  (to_bits (inv_mix_columns k))
    = to_bits
        (inv_mix_columns
           (from_bits (add_round_key 32 4 (to_bits st) (to_bits k)))).
  Proof.
    intros. rewrite !add_round_key_byte_add.
    rewrite inv_mix_columns_add_comm.
    autorewrite with conversions.
    reflexivity.
  Qed.
End MixColsAddRoundKey.
