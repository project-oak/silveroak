(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Import Circuit.Notations.

(* get the state of a circuit after running it on the specified input from the
   specified start state *)
Definition repeat_step {i o} (c : Circuit i o) input st : circuit_state c :=
  fold_left (fun st i => fst (step c st i)) input st.

(* Circuit equivalence relation that allows the first n timesteps to differ *)
Definition cequivn {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  (* there exists some relation between the circuit states... *)
  exists (R : circuit_state c1 -> circuit_state c2 -> Prop),
    (* ...and the relation holds after n timesteps of equal input for all inputs
       and all initial states *)
    (forall input st1 st2,
        length input = n ->
        R (repeat_step c1 input st1) (repeat_step c2 input st2))
    (* ...and if the relation holds, stepping each circuit on the same input
         results in the same output as well as new states on which the relation
         continues to hold *)
    /\ (forall s1 s2 input,
          R s1 s2 ->
          snd (step c1 s1 input) = snd (step c2 s2 input)
          /\ R (fst (step c1 s1 input)) (fst (step c2 s2 input))).

(* cequiv is transitive *)
Global Instance Transitive_cequivn {i o} n : Transitive (@cequivn i o n) | 10.
Proof.
  intros x y z [Rxy [? Hxy]] [Ryz [? Hyz]]. logical_simplify.
  exists (fun (st1 : circuit_state x) (st2 : circuit_state z) =>
       exists st3 : circuit_state y, Rxy st1 st3 /\ Ryz st3 st2).
  ssplit.
  { intro input; intros.
    exists (fold_left (fun st i => fst (step y st i)) input (reset_state y)).
    eauto. }
  { intros; logical_simplify.
    specialize (Hxy _ _ ltac:(eassumption) ltac:(eassumption)).
    specialize (Hyz _ _ ltac:(eassumption) ltac:(eassumption)).
    logical_simplify. ssplit; [ congruence | ]. eauto. }
Qed.

(* cequivn is symmetric *)
Global Instance Symmetric_cequivn {i o} n : Symmetric (@cequivn i o n) | 10.
Proof.
  intros x y [R [? HR]]. logical_simplify.
  exists (fun st1 st2 => R st2 st1). ssplit; [ solve [eauto] | ].
  intros. specialize (HR _ _ ltac:(eassumption) ltac:(eassumption)).
  logical_simplify. eauto.
Qed.

(* Note: cequivn is NOT reflexive in general. *)

Lemma skipn_fold_left_accumulate {A B C} (f : B -> A -> B * C) n ls b :
  skipn n (fold_left_accumulate f ls b)
  = fold_left_accumulate
      f (skipn n ls) (fold_left (fun b a => fst (f b a)) (firstn n ls) b).
Admitted.

(* equivalent circuits produce the same output on the same input after n
   timesteps *)
Lemma simulate_cequivn {i o} n (c1 c2 : Circuit i o) :
  cequivn n c1 c2 ->
  forall input, skipn n (simulate c1 input) = skipn n (simulate c2 input).
Proof.
  intros [R [Hstart Hpreserved]]; intros. logical_simplify. cbv [simulate].
  destr (length input <=? n); [ rewrite !skipn_all2 by length_hammer; reflexivity | ].
  rewrite !skipn_fold_left_accumulate.
  eapply fold_left_accumulate_double_invariant_In
    with (I:=fun st1 st2 acc1 acc2 =>
               R st1 st2 /\ acc1 = acc2).
  { ssplit; eauto. apply Hstart. length_hammer. }
  { intros; logical_simplify; subst.
    lazymatch goal with
    | H : forall _ _ _, R _ _ -> _ /\ _, HR : R _ _ |- context [step _ _ ?i] =>
    let H1 := fresh in
    let H2 := fresh in
    specialize (H _ _ i HR); destruct H as [H1 H2];
      rewrite ?H1, ?H2
    end.
    ssplit; eauto. }
  { intros; logical_simplify; subst. reflexivity. }
Qed.

Lemma cequivn_cequiv {i o} (c1 c2 : Circuit i o) :
  cequivn 0 c1 c2 -> cequiv c1 c2.
Proof.
  intros [R [Hstart Hstep]].
  specialize (Hstart nil (reset_state c1) (reset_state c2) eq_refl).
  cbn [fold_left] in Hstart. exists R; eauto.
Qed.

(* 0-equivalent circuits produce exactly the same output on the same input *)
Lemma simulate_cequivn0 {i o} (c1 c2 : Circuit i o) :
  cequivn 0 c1 c2 -> forall input, simulate c1 input = simulate c2 input.
Proof. auto using simulate_cequiv, cequivn_cequiv. Qed.

(* Proper instance allows rewriting under simulate *)
Global Instance Proper_simulate i o :
  Proper (cequivn 0 ==> eq ==> eq) (@simulate i o).
Proof. repeat intro; subst. eapply simulate_cequivn0; auto. Qed.

Lemma state_relation_fold_left_accumulate_step
      i o (c1 c2 : Circuit i o) (R : _ -> _ -> Prop) :
  (forall s1 s2 input,
      R s1 s2 ->
      snd (step c1 s1 input) = snd (step c2 s2 input)
      /\ R (fst (step c1 s1 input)) (fst (step c2 s2 input))) ->
  forall input s1 s2,
    R s1 s2 ->
    fold_left_accumulate (step c1) input s1
    = fold_left_accumulate (step c2) input s2.
Proof.
  intro HR. intros.
  apply fold_left_accumulate_double_invariant_In
    with (I:=fun s1 s2 acc1 acc2 =>
               R s1 s2 /\ acc1 = acc2).
  { eauto. }
  { intros s1' s2'; intros.
    logical_simplify; subst.
    specialize (HR s1' s2' ltac:(eassumption) ltac:(eassumption)).
    logical_simplify; subst. ssplit; [ assumption | congruence ]. }
  { intros; logical_simplify; subst; reflexivity. }
Qed.

Lemma state_relation_repeat_step
      i o (c1 c2 : Circuit i o) (R : _ -> _ -> Prop) :
  (forall s1 s2 input,
      R s1 s2 ->
      snd (step c1 s1 input) = snd (step c2 s2 input)
      /\ R (fst (step c1 s1 input)) (fst (step c2 s2 input))) ->
  forall input s1 s2,
    R s1 s2 -> R (repeat_step c1 input s1) (repeat_step c2 input s2).
Proof.
  intro HR. intros. cbv [repeat_step].
  eapply fold_left_double_invariant with (I:=R).
  { eauto. }
  { intros s1' s2'; intros.
    logical_simplify; subst.
    specialize (HR s1' s2' ltac:(eassumption) ltac:(eassumption)).
    logical_simplify; subst; auto. }
  { intros; logical_simplify; auto. }
Qed.

Lemma repeat_step_app {i o} (c : Circuit i o) input1 input2 st :
  repeat_step c (input1 ++ input2) st
  = repeat_step c input2 (repeat_step c input1 st).
Proof. apply fold_left_app. Qed.

Lemma repeat_step_compose {i t o} c1 c2 input st :
  repeat_step (@Compose _ _ i t o c1 c2) input st
  = (repeat_step c1 input (fst st),
     repeat_step c2 (fold_left_accumulate (step c1) input (fst st)) (snd st)).
Proof.
  cbv [repeat_step]. revert st.
  induction input; [ destruct st; reflexivity | ].
  intros; cbn [circuit_state] in *. destruct_products; cbn [fst snd].
  autorewrite with push_list_fold push_fold_acc.
  rewrite IHinput. cbn [step].
  repeat (destruct_pair_let; cbn [fst snd]).
  reflexivity.
Qed.

Lemma repeat_step_First {i t o} (c : Circuit i o) input st :
  repeat_step (First (t:=t) c) input st = repeat_step c (map fst input) st.
Proof.
  cbv [repeat_step]. revert st.
  induction input; [ reflexivity | ].
  intros; cbn [circuit_state] in *. destruct_products; cbn [fst snd].
  autorewrite with push_list_fold push_fold_acc.
  rewrite IHinput. cbn [step].
  repeat (destruct_pair_let; cbn [fst snd]).
  reflexivity.
Qed.

Lemma repeat_step_Second {i t o} (c : Circuit i o) input st :
  repeat_step (Second (t:=t) c) input st = repeat_step c (map snd input) st.
Proof.
  cbv [repeat_step]. revert st.
  induction input; [ reflexivity | ].
  intros; cbn [circuit_state] in *. destruct_products; cbn [fst snd].
  autorewrite with push_list_fold push_fold_acc.
  rewrite IHinput. cbn [step].
  repeat (destruct_pair_let; cbn [fst snd]).
  reflexivity.
Qed.

Lemma cequivn_compose {i t o} n m (a b : Circuit i t) (c d : Circuit t o) :
  cequivn n a b -> cequivn m c d ->
  cequivn (n + m) (a >==> c) (b >==> d).
Proof.
  intros [Rab [? Hab]] [Rcd [? Hcd]].
  exists (fun st1 st2 => Rab (fst st1) (fst st2) /\ Rcd (snd st1) (snd st2)).
  ssplit.
  { intro input; intros. rewrite <-(firstn_skipn n input).
    rewrite !repeat_step_app, !repeat_step_compose.
    cbn [fst snd]. assert (length (firstn n input) = n) by length_hammer.
    assert (length (skipn n input) = m) by length_hammer.
    ssplit; [ apply state_relation_repeat_step; solve [eauto] | ].
    erewrite state_relation_fold_left_accumulate_step by eauto.
    match goal with H : _ |- _ => apply H; length_hammer end. }
  { cbn [circuit_state step]. intros; logical_simplify.
    pose proof (fun i => proj1 (Hab _ _ i ltac:(eassumption))) as Hab1.
    pose proof (fun i => proj2 (Hab _ _ i ltac:(eassumption))) as Hab2.
    pose proof (fun i => proj1 (Hcd _ _ i ltac:(eassumption))) as Hcd1.
    pose proof (fun i => proj2 (Hcd _ _ i ltac:(eassumption))) as Hcd2.
    clear Hab Hcd. logical_simplify.
    repeat (destruct_pair_let; cbn [fst snd]).
    rewrite ?Hab1, ?Hcd1. ssplit; eauto. }
Qed.

(* cequivn n c1 c2 -> cequivn n (First c1) (First c2) *)
Global Instance Proper_First {i o t} n :
  Proper (cequivn n ==> cequivn n) (@First _ _ i o t).
Proof.
  intros x y [Rxy [? Hxy]].
  exists Rxy; ssplit.
  { intros. rewrite !repeat_step_First.
    match goal with H : _ |- _ => apply H; length_hammer end. }
  { cbn [circuit_state step]. intros; logical_simplify.
    pose proof (fun i => proj1 (Hxy _ _ i ltac:(eassumption))) as Hxy1.
    pose proof (fun i => proj2 (Hxy _ _ i ltac:(eassumption))) as Hxy2.
    clear Hxy. logical_simplify. repeat (destruct_pair_let; cbn [fst snd]).
    rewrite Hxy1. ssplit; eauto. }
Qed.

(* cequivn n c1 c2 -> cequivn n (Second c1) (Second c2) *)
Global Instance Proper_Second {i o t} n :
  Proper (cequivn n ==> cequivn n) (@Second _ _ i o t).
Proof.
  intros x y [Rxy [? Hxy]].
  exists Rxy; ssplit.
  { intros. rewrite !repeat_step_Second.
    match goal with H : _ |- _ => apply H; length_hammer end. }
  { cbn [circuit_state step]. intros; logical_simplify.
    pose proof (fun i => proj1 (Hxy _ _ i ltac:(eassumption))) as Hxy1.
    pose proof (fun i => proj2 (Hxy _ _ i ltac:(eassumption))) as Hxy2.
    clear Hxy. logical_simplify. repeat (destruct_pair_let; cbn [fst snd]).
    rewrite Hxy1. ssplit; eauto. }
Qed.
