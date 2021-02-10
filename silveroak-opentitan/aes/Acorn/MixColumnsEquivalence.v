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
Import ListNotations.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AcornAes.Pkg.
Require Import AcornAes.MixColumnsCircuit.
Import StateTypeConversions.LittleEndian.

Existing Instance CombinationalSemantics.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma aes_transpose_correct n m (v : combType (Vec (Vec (Vec Bit 8) n) m)) :
    aes_transpose [v] = [transpose v].
  Admitted.

  Lemma mix_single_column_equiv (is_decrypt : bool) (col : Vector.t byte 4) :
    unIdent (aes_mix_single_column [is_decrypt] [col])
    = [if is_decrypt
       then map byte_to_bitvec
                (MixColumns.inv_mix_single_column (map bitvec_to_byte col))
       else map byte_to_bitvec
                (MixColumns.mix_single_column (map bitvec_to_byte col))].
  Admitted.

  Lemma mix_columns_equiv (is_decrypt : bool) (st : state) :
    combinational (aes_mix_columns [is_decrypt] [st])
    = [AES256.aes_mix_columns_circuit_spec is_decrypt st].
  Proof.
    cbv [aes_mix_columns combinational]. simpl_ident.
    rewrite aes_transpose_correct.
    rewrite (peel_singleton (A:=Vec (Vec Bit 8) 4)).
    rewrite map_map.
    erewrite map_ext by apply mix_single_column_equiv.
    rewrite (unpeel_singleton (B:=Vec (Vec Bit 8) 4)) by congruence.
    rewrite aes_transpose_correct.
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
