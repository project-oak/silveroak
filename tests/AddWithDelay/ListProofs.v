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
Require Import Cava.Acorn.SequentialProperties.
Require Import Cava.Lib.UnsignedAdders.

Require Import Tests.AddWithDelay.AddWithDelay.
Local Open Scope nat_scope.

Definition bvadd {n} (a b : Signal.combType (Vec Bit n)) : Signal.combType (Vec Bit n) :=
  N2Bv_sized n (Bv2N a + Bv2N b).

Definition bvzero {n} : Signal.combType (Vec Bit n) := N2Bv_sized n 0.

Definition addWithDelaySpecF
           (input : nat -> Signal.combType (Vec Bit 8)) : nat -> Signal.combType (Vec Bit 8) :=
  fix out (t : nat) :=
    match t with
    | 0 => bvzero (* first round is just a delay *)
    | 1 =>
      (* second round is first input (because initial feedback = 0) *)
      input 0
    | S (S t') =>
      (* if t > 2, out(t) = in(t-1) + out(t-2) *)
      bvadd (input (S t')) (out t')
    end.

Definition addNSpec {n} (a b : seqType (Vec Bit n)) :=
  map2 bvadd a b.

(* TODO: rename typeclass arguments *)
Lemma addNCorrect n (a b : list (Bvector n)) :
  sequential (addN (semantics:=SequentialCombSemantics) (a, b)) = addNSpec a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : seqsimpl.

Lemma addWithDelayStepCorrect :
  forall (i : Bvector 8) (s : Bvector 8),
    sequential ((addN >=> delay >=> fork2) ([i], [s]))
    = ([bvzero; bvadd i s], [bvzero; bvadd i s]).
Proof.
  intros. seqsimpl. reflexivity.
Qed.
Hint Rewrite addWithDelayStepCorrect using solve [eauto] : seqsimpl.

Lemma Bv2N_bvzero n : Bv2N (@bvzero n) = 0%N.
Proof.
  cbv [bvzero N2Bv_sized Bvect_false].
  induction n; intros; [ reflexivity | ].
  rewrite const_cons. cbn [Bv2N].
  rewrite IHn. reflexivity.
Qed.

Lemma bvadd_bvzero_l {n} (x : Bvector n) : bvadd x bvzero = x.
Proof.
  cbv [bvadd]. rewrite Bv2N_bvzero.
  rewrite N.add_0_r, N2Bv_sized_Bv2N.
  reflexivity.
Qed.

Lemma addWithDelayCorrect (i : list (Bvector 8)) :
  sequential (addWithDelay i) = map (fun t => addWithDelaySpecF (fun n => nth n i bvzero) t)
                                    (seq 0 (if length i =? 0 then 0 else S (length i))).
Proof.
  intros; cbv [addWithDelay].
  eapply (loop_invariant_alt (B:=Vec Bit 8) (C:=Vec Bit 8))
    with (I:=fun t acc feedback =>
               0 < t
               /\ feedback = [nth (t-1) acc bvzero; nth t acc bvzero]
               /\ acc = map (fun t => addWithDelaySpecF
                                    (fun n => nth n i bvzero) t) (seq 0 (S t))).
  { (* invariant is satisfied at start *)
    destruct i; [ ssplit; reflexivity | ].
    seqsimpl. autorewrite with natsimpl.
    cbn [nth map seq addWithDelaySpecF].
    change (Signal.defaultCombValue (Vec Bit 8)) with (@bvzero 8).
    rewrite bvadd_bvzero_l. ssplit; (reflexivity || lia). }
  { (* invariant holds through loop *)
    intros *. intros [Ht [Hfeedback Hacc]]. cbv zeta; intros.
    subst. seqsimpl.
    rewrite seq_S, map_app. cbn [map].
    rewrite !overlap_snoc_cons by length_hammer.
    autorewrite with push_nth push_length natsimpl.
    cbn [nth]. ssplit; [ lia | reflexivity | ].
    rewrite !seq_S, !map_app. cbn [map].
    autorewrite with natsimpl. cbn [addWithDelaySpecF].
    destruct t; [ lia | ].
    rewrite !seq_S, !map_app. cbn [map].
    autorewrite with natsimpl push_length push_nth.
    cbn [nth]. rewrite <-!app_assoc.
    reflexivity. }
  { (* invariant implies postcondition *)
    intros *; intros [Ht [Hfeedback Hacc]]; intros.
    subst. destruct i; autorewrite with push_length in *; [ lia | ].
    reflexivity. }
Qed.
