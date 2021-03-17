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

Require Import Coq.setoid_ring.Ring.
Require Import Cava.Cava.
Require Import Cava.CavaProperties.
Require Import AesSpec.AES256.
Require Import AesSpec.Polynomial.
Require Import AesSpec.StateTypeConversions.
Require Import AesImpl.Pkg.
Require Import AesImpl.MixColumnsCircuit.
Import StateTypeConversions.LittleEndian.

Existing Instance MixColumns.byteops.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma aes_transpose_correct n m (v : combType (Vec (Vec (Vec Bit 8) n) m)) :
    aes_transpose v = transpose v.
  Proof. cbv [aes_transpose]; simpl_ident; reflexivity. Qed.

  Lemma poly_to_byte_to_bitvec p :
    length p = 8 -> byte_to_bitvec (MixColumns.poly_to_byte p) = of_list_sized false 8 p.
  Proof.
    intros; destruct_lists_by_length.
    repeat match goal with b : bool |- _ => destruct b end; reflexivity.
  Qed.

  Lemma bitvec_to_byte_to_poly bv :
    MixColumns.byte_to_poly (bitvec_to_byte bv) = Vector.to_list bv.
  Proof.
    constant_bitvec_cases bv; reflexivity.
  Qed.

  Lemma xorV_is_add (b1 b2 : byte) :
    Vec.xor (n:=8) (b1, b2)
    = byte_to_bitvec (Polynomial.fadd (bitvec_to_byte b1)
                                      (bitvec_to_byte b2)).
  Proof.
    simpl_ident. fequal_list.
    cbv [Polynomial.fadd MixColumns.byteops].
    rewrite poly_to_byte_to_bitvec, !bitvec_to_byte_to_poly by length_hammer.
    cbv [Polynomial.add_poly].
    apply to_list_inj. autorewrite with push_to_list push_extend.
    rewrite to_list_of_list_sized by length_hammer.
    reflexivity.
  Qed.

  Lemma aes_mul2_correct (b : byte) :
    aes_mul2 b
    = byte_to_bitvec (Polynomial.fmul Byte.x02
                                      (bitvec_to_byte b)).
  Proof.
    constant_bitvec_cases b; vm_compute; reflexivity.
  Qed.

  Lemma aes_mul4_correct (b : byte) :
    aes_mul4 b
    = byte_to_bitvec (Polynomial.fmul Byte.x04
                                      (bitvec_to_byte b)).
  Proof.
    constant_bitvec_cases b; vm_compute; reflexivity.
  Qed.

  Hint Rewrite xorV_is_add using solve [eauto] : simpl_ident.
  Hint Rewrite aes_mul2_correct using solve [eauto] : simpl_ident.
  Hint Rewrite aes_mul4_correct using solve [eauto] : simpl_ident.

  Local Open Scope poly_scope.

  Lemma zero_byte_correct : bitvec_to_byte zero_byte = fzero.
  Proof. reflexivity. Qed.
  Hint Rewrite zero_byte_correct using solve [eauto] : simpl_ident.

  Ltac prering :=
    change Byte.x03 with (Byte.x02 + Byte.x01);
    change Byte.x04 with (Byte.x02 * Byte.x02);
    change Byte.x05 with (Byte.x02 * Byte.x02 + Byte.x01);
    change Byte.x06 with (Byte.x02 * (Byte.x02 + Byte.x01));
    change Byte.x07 with (Byte.x02 * (Byte.x02 + Byte.x01) + Byte.x01);
    change Byte.x08 with (Byte.x02 * (Byte.x02 * Byte.x02));
    change Byte.x09 with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x01);
    change Byte.x0a with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02);
    change Byte.x0b with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 + Byte.x01);
    change Byte.x0c with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 * Byte.x02);
    change Byte.x0d with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 * Byte.x02 + Byte.x01);
    change Byte.x0e with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 * (Byte.x02 + Byte.x01));
    change Byte.x0e with (Byte.x02 * (Byte.x02 * Byte.x02) + Byte.x02 * (Byte.x02 + Byte.x01) + Byte.x01);
    change Byte.x01 with fone.

  Add Ring bytering : MixColumns.ByteTheory (preprocess [prering]).

  Lemma mix_single_column_equiv (is_decrypt : bool) (col : Vector.t byte 4) :
    aes_mix_single_column is_decrypt col
    = if is_decrypt
      then Vector.map
             byte_to_bitvec
             (MixColumns.inv_mix_single_column (Vector.map bitvec_to_byte col))
      else Vector.map
             byte_to_bitvec
             (MixColumns.mix_single_column (Vector.map bitvec_to_byte col)).
  Proof.
    constant_vector_simpl col.
    unfold MixColumns.inv_mix_single_column, MixColumns.mix_single_column.
    cbn [Vector.map].
    autorewrite with push_vector_map vsimpl.
    autorewrite with push_vector_fold vsimpl.

    unfold aes_mix_single_column.
    (* reduce size of term by simplifying indexConst for constant vectors immediately *)
    repeat lazymatch goal with
           | |- context [(@indexConst _ ?cava ?t ?sz (Vector.cons ?A ?x ?n ?v) ?i)] =>
             let y := constr:(@indexConst _ cava t sz (Vector.cons A x n v) i) in
             let z := (eval cbn in y) in
             change y with z
           end.
    simpl_ident.
    cbn [localSignal CombinationalSemantics].
    simpl_ident.
    destruct is_decrypt.
    all: cbn [nth_default map]; simpl_ident.
    all: repeat rewrite byte_to_bitvec_to_byte.
    all: fequal_vector; f_equal.
    all: ring.
  Qed.

  Lemma mix_columns_equiv (is_decrypt : bool) (st : state) :
    aes_mix_columns is_decrypt st
    = AES256.aes_mix_columns_circuit_spec is_decrypt st.
  Proof.
    cbv [aes_mix_columns mcompose]. simpl_ident.
    rewrite ! aes_transpose_correct by lia.
    erewrite Vector.map_ext by apply mix_single_column_equiv.
    cbv [AES256.aes_mix_columns_circuit_spec
           AES256.mix_columns AES256.inv_mix_columns
           MixColumns.mix_columns MixColumns.inv_mix_columns].
    cbv [from_flat to_flat BigEndian.to_rows BigEndian.from_rows].
    autorewrite with conversions.
    (* consolidate all the repeated maps *)
    rewrite !transpose_map_map, !Vector.map_map.
    rewrite <-!transpose_map_map, !Vector.map_map.
    destruct is_decrypt;
      repeat lazymatch goal with
             | |- [_] = [_] => apply f_equal
             | |- transpose _ = transpose _ => apply f_equal
             | |- map _ ?v = map _ ?v => apply map_ext; intros
             | _ => reflexivity
             end.
  Qed.
End Equivalence.
