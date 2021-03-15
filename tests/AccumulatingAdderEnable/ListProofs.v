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

From Coq Require Import Arith.PeanoNat NArith.NArith Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bvector.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import coqutil.Tactics.Tactics.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.CombinationalProperties.
Require Import Cava.Lib.UnsignedAdders.

Require Import Tests.AccumulatingAdderEnable.AccumulatingAdderEnable.

Definition bvadd {n} (a b : Signal.combType (Vec Bit n)) : Signal.combType (Vec Bit n) :=
  N2Bv_sized n (Bv2N a + Bv2N b).

Definition bvzero {n} : Signal.combType (Vec Bit n) := N2Bv_sized n 0.

Definition bvsum {n} (l : list (Bvector n)) : Bvector n :=
  fold_left bvadd l (N2Bv_sized n 0).

Definition accumulatingAdderEnableSpec
           (i : list (combType (Vec Bit 8) * combType Bit))
  : list (combType (Vec Bit 8)) * combType (Vec Bit 8) :=
  fold_left
    (fun acc_st v_en =>
       let sum := bvadd (snd acc_st) (fst v_en) in
       (fst acc_st ++ [sum], if (snd v_en : bool) then sum else snd acc_st))
    i ([], bvzero).

Lemma addNCorrect n (a b : Vector.t bool n) :
  unIdent (addN (a, b)) = bvadd a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : simpl_ident.

Lemma bvadd_comm {n} a b : @bvadd n a b = bvadd b a.
Proof. cbv [bvadd]. rewrite N.add_comm. reflexivity. Qed.

Lemma accumulatingAdderEnableSpec_snoc xs x :
  accumulatingAdderEnableSpec (xs ++ [x]) =
  let acc_st := accumulatingAdderEnableSpec xs in
  let sum := bvadd (snd acc_st) (fst x) in
  (fst acc_st ++ [sum], if (snd x : bool) then sum else snd acc_st).
Proof.
  cbv [accumulatingAdderEnableSpec].
  autorewrite with pull_snoc. cbn [fst snd].
  reflexivity.
Qed.

Lemma accumulatingAdderEnableCorrect (i : list (Bvector 8 * bool)) :
  multistep accumulatingAdderEnable i = fst (accumulatingAdderEnableSpec i).
Proof.
  intros; cbv [accumulatingAdderEnable].
  eapply multistep_LoopCE_invariant
    with (I:=fun t st _ acc =>
               st = snd (accumulatingAdderEnableSpec (firstn t i))
               /\ acc = fst (accumulatingAdderEnableSpec (firstn t i))).
  { (* invariant holds after first step *)
    split; reflexivity. }
  { (* invariant holds through body *)
    cbv zeta. intros ? ? ? ? d; intros; logical_simplify; subst.
    cbv [step mcompose]. simpl_ident.
    rewrite firstn_succ_snoc with (d0:=d) by length_hammer.
    cbv [combType Bvector] in *. autorewrite with push_length natsimpl.
    cbv [bvsum]. autorewrite with pull_snoc.
    rewrite accumulatingAdderEnableSpec_snoc. cbn [fst snd].
    rewrite bvadd_comm. split; reflexivity. }
  { (* invariant implies postcondition *)
    intros; logical_simplify; subst.
    rewrite firstn_all; reflexivity. }
Qed.
