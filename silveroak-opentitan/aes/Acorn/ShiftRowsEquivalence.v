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
Require Import AcornAes.ShiftRowsCircuit.
Import StateTypeConversions.LittleEndian.

Existing Instance CombinationalSemantics.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma shift_rows_equiv (is_decrypt : bool) (st : state) :
    combinational (aes_shift_rows [is_decrypt] [st])
    = [AES256.aes_shift_rows_circuit_spec is_decrypt st].
  Proof.
    cbv [aes_shift_rows combinational]. simpl_ident.
    rewrite !(@indexConst_singleton (Vec (Vec Bit 8) 4)).

    (* break state vector into 16 bytes *)
    constant_vector_simpl st.
    repeat lazymatch goal with
           | v := @hd (t byte 4) _ _ |- _ =>
                  constant_vector_simpl v; subst v
           | v := @tl (t byte 4) _ _ |- _ => subst v
           | v := _ : t _ 0 |- _ => clear v
           end.
    cbn [nth_default].

    (* simplify RHS (specification) *)
    cbv [aes_shift_rows_circuit_spec
           AES256.shift_rows AES256.inv_shift_rows
           ShiftRows.shift_rows ShiftRows.inv_shift_rows].
    cbv [to_flat from_flat BigEndian.from_list_rows BigEndian.to_list_rows].
    autorewrite with conversions push_length push_to_list.
    cbn [List.map map]. autorewrite with push_to_list.
    cbv [ShiftRows.shift_rows_start ShiftRows.inv_shift_row].
    autorewrite with push_length. cbn [seq map2].
    autorewrite with push_of_list_sized. cbn [map].

    (* simplify LHS (implementation) *)
    cbv [aes_circ_byte_shift]. simpl_ident.
    repeat lazymatch goal with
           | |- context [map (@indexConst _ _ ?A _ [?x]%list) ?y] =>
             erewrite map_ext with (f:=@indexConst seqType _ A _ [x]%list)
                                   (g:=fun n => [nth_default (defaultCombValue A) n x])
               by (intros; rewrite !(@indexConst_singleton (Vec Bit 8));
                   reflexivity)
           end.
    rewrite !map_map.
    rewrite !(@unpeel_singleton _ (Vec Bit 8)) by congruence.
    rewrite !(@muxPair_correct (Vec (Vec Bit 8) 4)).
    cbn [map].
    repeat match goal with
           | |- context [Nat.modulo ?n ?m] => compute_expr (Nat.modulo n m)
           end.
    cbv [unpeel CombinationalSemantics unpeelVecList].
    cbn [map length fold_left PeanoNat.Nat.max seq List.nth
             List.map nth_default List.rev app].

    (* prove the two sides are equivalent *)
    destruct is_decrypt.
    { fequal_list; fequal_vector;
        cbn - [bitvec_to_byte byte_to_bitvec];
        rewrite !bitvec_to_byte_to_bitvec; reflexivity. }
    { fequal_list; fequal_vector;
        cbn - [bitvec_to_byte byte_to_bitvec];
        rewrite !bitvec_to_byte_to_bitvec; reflexivity. }
  Qed.
End Equivalence.
