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
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Acorn.MonadFacts.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.BitVectorOps.
Import ListNotations.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AcornAes.AddRoundKey.

Existing Instance CombinationalSemantics.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma add_round_key_equiv (k : key) (st : state) :
    combinational (add_round_key [k] [st])
    = [to_cols_bitvecs (AES256.add_round_key (from_cols_bitvecs st)
                                             (from_cols_bitvecs k))].
  Proof.
    cbv [AES256.add_round_key
           AcornAes.AddRoundKey.add_round_key
           AesSpec.AddRoundKey.add_round_key].
    cbv [xor4x4V xor4xV]. cbv [Bvector.BVxor].
    erewrite (zipWith_unIdent (A:=Vec (Vec Bit 8) 4)
                              (B:=Vec (Vec Bit 8) 4)
                              (C:=Vec (Vec Bit 8) 4));
      [ | congruence | ].
    2:{ cbn [fst snd]. intros.
        erewrite (zipWith_unIdent (A:=Vec Bit 8)
                                  (B:=Vec Bit 8)
                                  (C:=Vec Bit 8))
          by first [ congruence
                   | intros; rewrite xorV_unIdent by congruence;
                     reflexivity ].
        reflexivity. }
    cbv [to_cols_bitvecs from_cols_bitvecs]. f_equal.
    autorewrite with conversions.
    cbn [fst snd]. rewrite map2_map, map_map2.
    rewrite map2_swap.
    erewrite map2_ext; [ reflexivity | ].
    intros. autorewrite with simpl_ident.
    erewrite map2_ext
      by (intros; autorewrite with simpl_ident;
          cbn [fst snd]; reflexivity).
    cbn [combType].
    rewrite <-map2_reshape, !reshape_flatten.
    rewrite map2_swap. apply map2_ext; intros.
    rewrite map2_swap. apply map2_ext; intros.
    intros; apply Bool.xorb_comm.
  Qed.
End Equivalence.
