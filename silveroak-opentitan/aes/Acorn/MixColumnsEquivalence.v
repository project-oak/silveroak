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
Require Import Coq.micromega.Lia.
Require Import Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monads.
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Acorn.CombinationalProperties.
Require Import Cava.Acorn.MonadFacts.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.BitVectorOps.
Import ListNotations VectorNotations.
Local Open Scope list_scope.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AcornAes.Pkg.
Require Import AcornAes.MixColumnsCircuit.
Import StateTypeConversions.LittleEndian.

Existing Instance CombinationalSemantics.
Existing Instance MixColumns.byteops.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma aes_transpose_correct n m (v : combType (Vec (Vec (Vec Bit 8) n) m)) :
    m <> 0 ->
    n <> 0 ->
    aes_transpose v = transpose v.
  Proof.
    intros Hm Hn.
    unfold aes_transpose.
    cbv [unpeel peel Combinational.CombinationalSemantics].
    rewrite ! map_id.
    reflexivity.
  Qed.

  Lemma poly_to_byte_to_bitvec p :
    length p = 8 -> byte_to_bitvec (MixColumns.poly_to_byte p) = of_list_sized false 8 p.
  Proof.
    intros; destruct_lists_by_length.
    repeat match goal with b : bool |- _ => destruct b end; reflexivity.
  Qed.
  Lemma bitvec_to_byte_to_poly bv :
    MixColumns.byte_to_poly (bitvec_to_byte bv) = to_list bv.
  Proof.
    constant_bitvec_cases bv; reflexivity.
  Qed.

  Lemma xorV_is_add (b1 b2 : byte) :
    unIdent (xorV (n:=8) (b1, b2))
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

  Lemma xorv_is_add (b1 b2 : byte) :
    unIdent (xorv (n:=8) b1 b2)
    = byte_to_bitvec (Polynomial.fadd (bitvec_to_byte b1)
                                      (bitvec_to_byte b2)).
  Proof. apply xorV_is_add. Qed.

  Lemma aes_mul2_correct (b : byte) :
    unIdent (aes_mul2 b)
    = byte_to_bitvec (Polynomial.fmul Byte.x02
                                      (bitvec_to_byte b)).
  Proof.
    constant_bitvec_cases b; vm_compute; reflexivity.
  Qed.

  Lemma aes_mul4_correct (b : byte) :
    unIdent (aes_mul4 b)
    = byte_to_bitvec (Polynomial.fmul Byte.x04
                                      (bitvec_to_byte b)).
  Proof.
    constant_bitvec_cases b; vm_compute; reflexivity.
  Qed.

  Lemma mix_single_column_equiv (is_decrypt : bool) (col : Vector.t byte 4) :
    unIdent (aes_mix_single_column is_decrypt col)
    = if is_decrypt
       then map byte_to_bitvec
                (MixColumns.inv_mix_single_column (map bitvec_to_byte col))
       else map byte_to_bitvec
                (MixColumns.mix_single_column (map bitvec_to_byte col)).
  Proof.
    (* simplify LHS *)
    cbv [aes_mix_single_column]. simpl_ident.
    constant_vector_simpl col.
    repeat lazymatch goal with
           | |- context [(@indexConst _ _ ?t ?n [?v])] =>
             rewrite !(@indexConst_singleton t n); cbn [nth_default map]
           | |- context [unIdent (@xorv _ _ 8 [?b1] [?b2])] =>
             rewrite !xorv_is_add
           | |- context [unIdent (xorV ([?b1], [?b2]))] =>
             rewrite !xorV_is_add
           | |- context [unIdent (aes_mul2 [?b])] =>
             rewrite !aes_mul2_correct
           | |- context [unIdent (aes_mul4 [?b])] =>
             rewrite !aes_mul4_correct
           | |- context [bitvec_to_byte (byte_to_bitvec _)] =>
             rewrite !byte_to_bitvec_to_byte
           | |- context [byte_to_bitvec (bitvec_to_byte _)] =>
             rewrite !bitvec_to_byte_to_bitvec
           | |- context [(@unpeel _ _ ?t ?n
                                 [[?x0]%list;[?x1]%list;[?x2]%list;[?x3]%list
                                 ]%vector)] =>
             (* simplify an unpeel with 4 elements that are all singletons *)
             change (@unpeel _ _ t n
                             [[?x0]%list;[?x1]%list;[?x2]%list;[?x3]%list
                             ]%vector)
               with [[x0;x1;x2;x3]%vector]
           end.
  Admitted.

  Lemma mix_columns_equiv (is_decrypt : bool) (st : state) :
    combinational (aes_mix_columns is_decrypt st)
    = AES256.aes_mix_columns_circuit_spec is_decrypt st.
  Proof.
    cbv [aes_mix_columns combinational]. simpl_ident.
    rewrite ! aes_transpose_correct by lia.
    erewrite map_ext by apply mix_single_column_equiv.
    cbv [AES256.aes_mix_columns_circuit_spec
           AES256.mix_columns AES256.inv_mix_columns
           MixColumns.mix_columns MixColumns.inv_mix_columns].
    cbv [from_flat to_flat BigEndian.to_rows BigEndian.from_rows].
    autorewrite with conversions.
    (* consolidate all the repeated maps *)
    rewrite !transpose_map_map, !map_map.
    rewrite <-!transpose_map_map, !map_map.
    destruct is_decrypt;
      repeat lazymatch goal with
             | |- [_] = [_] => apply f_equal
             | |- transpose _ = transpose _ => apply f_equal
             | |- map _ ?v = map _ ?v => apply map_ext; intros
             | _ => reflexivity
             end.
  Qed.
End Equivalence.
