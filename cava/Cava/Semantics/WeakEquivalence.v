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
Require Import Coq.Classes.Morphisms.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.

Definition mealy {i o} (c : Circuit i o)
  : Circuit (i * circuit_state c) (o * circuit_state c) :=
  Comb (fun '(input, st) =>
          let st_out := step c st input in
          (snd st_out, fst st_out)).

(* Weaker notion of circuit equivalence that allows circuits to have equal
   behavior only for certain timesteps

   If weak_cequiv n m c1 c2 holds, then after the first n timesteps from a
   reset, c1 will compute the same values as c2 but take m additional timesteps
   for each step taken by c2.
 *)
Definition cequivn {i o} (n m : nat) (c1 c2 : Circuit i o) : Prop :=
  
  (* there exists some relation between the circuit states and a counter value... *)
  exists (R : nat -> circuit_state c1 -> circuit_state c2 -> Prop),
    (* ...and the relation holds after the first n timesteps for all inputs *)
    (forall input,
        length input = n ->
        R 0 (fold_left (fun st i => fst (step c1 st i)) input (reset_state c1))
          (fold_left (fun st i => fst (step c2 st i)) input (reset_state c2)))
    (* ... and if the relation holds for a 0 counter, then the outputs must
       match if the inputs are the same *)
    /\ (forall s1 s2 input,
          R 0 s1 s2 ->
          snd (step c1 s1 input) = snd (step c2 s2 input))
          
    (* ...and if the relation holds, stepping each circuit on the same input
         results in the same output as well as new states on which the relation
         continues to hold *)
    /\ (forall s1 s2 input,
          R s1 s2 ->
          snd (step c1 s1 input) = snd (step c2 s2 input)
          /\ R (fst (step c1 s1 input)) (fst (step c2 s2 input))).

(* Circuit equivalence relation that allows the first n timesteps to differ *)
Definition cequivn {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  (* there exists some relation between the circuit states... *)
  exists (R : circuit_state c1 -> circuit_state c2 -> Prop),
    (* ...and the relation holds after the first n timesteps for all inputs *)
    (forall input,
        length input = n ->
        R (fold_left (fun st i => fst (step c1 st i)) input (reset_state c1))
          (fold_left (fun st i => fst (step c2 st i)) input (reset_state c2)))
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

(* cequivn is reflexive *)
Global Instance Reflexive_cequivn {i o} n : Reflexive (@cequivn i o n) | 10.
Proof.
  repeat intro. exists eq. ssplit; [ reflexivity | ].
  intros; subst. ssplit; reflexivity.
Qed.

(* cequivn is symmetric *)
Global Instance Symmetric_cequivn {i o} n : Symmetric (@cequivn i o n) | 10.
Proof.
  intros x y [R [? HR]]. logical_simplify.
  exists (fun st1 st2 => R st2 st1). ssplit; [ assumption | ].
  intros. specialize (HR _ _ ltac:(eassumption) ltac:(eassumption)).
  logical_simplify. eauto.
Qed.

(* cequivn is an equivalence relation *)
Global Instance Equivalence_cequivn {i o} n : Equivalence (@cequivn i o n) | 10.
Proof. constructor; typeclasses eauto. Qed.

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

Lemma cequivn_cequiv_iff {i o} (c1 c2 : Circuit i o) :
  cequivn 0 c1 c2 <-> cequiv c1 c2.
Proof.
  split.
  { intros [R [Hstart Hstep]].
    specialize (Hstart nil eq_refl). cbn [fold_left] in Hstart.
    exists R; eauto. }
  { intros [R [Hstart Hstep]].
    exists R; ssplit; [ | solve [eauto] ].
    intro input; destruct input; [ | length_hammer ].
    intros; cbn [fold_left]. assumption. }
Qed.

(* 0-equivalent circuits produce exactly the same output on the same input *)
Lemma simulate_cequivn0 {i o} (c1 c2 : Circuit i o) :
  cequivn 0 c1 c2 -> forall input, simulate c1 input = simulate c2 input.
Proof.
  rewrite cequivn_cequiv_iff.
  apply simulate_cequiv.
Qed.

(* Proper instance allows rewriting under simulate *)
Global Instance Proper_simulate i o :
  Proper (cequivn 0 ==> eq ==> eq) (@simulate i o).
Proof. repeat intro; subst. eapply simulate_cequivn0; auto. Qed.

Global Instance Proper_Compose {i t o} :
  Proper (cequivn n ==> cequivn ==> cequivn) (@Compose _ _ i t o).
Proof.
  intros a b [Rab [? Hab]].
  intros c d [Rcd [? Hcd]].
  exists (fun st1 st2 => Rab (fst st1) (fst st2) /\ Rcd (snd st1) (snd st2)).
  ssplit; [ assumption .. | ].
  cbn [circuit_state step]. intros; logical_simplify.
  pose proof (fun i => proj1 (Hab _ _ i ltac:(eassumption))) as Hab1.
  pose proof (fun i => proj2 (Hab _ _ i ltac:(eassumption))) as Hab2.
  pose proof (fun i => proj1 (Hcd _ _ i ltac:(eassumption))) as Hcd1.
  pose proof (fun i => proj2 (Hcd _ _ i ltac:(eassumption))) as Hcd2.
  clear Hab Hcd. logical_simplify.
  repeat (destruct_pair_let; cbn [fst snd]).
  rewrite ?Hab1, ?Hcd1. ssplit; eauto.
Qed.

(* cequivn c1 c2 -> cequivn (First c1) (First c2) *)
Global Instance Proper_First {i o t} :
  Proper (cequivn ==> cequivn) (@First _ _ i o t).
Proof.
  intros x y [Rxy [? Hxy]].
  exists Rxy; ssplit; [ assumption | ].
  cbn [circuit_state step]. intros; logical_simplify.
  pose proof (fun i => proj1 (Hxy _ _ i ltac:(eassumption))) as Hxy1.
  pose proof (fun i => proj2 (Hxy _ _ i ltac:(eassumption))) as Hxy2.
  clear Hxy. logical_simplify. repeat (destruct_pair_let; cbn [fst snd]).
  rewrite Hxy1. ssplit; eauto.
Qed.

(* cequivn c1 c2 -> cequivn (Second c1) (Second c2) *)
Global Instance Proper_Second {i o t} :
  Proper (cequivn ==> cequivn) (@Second _ _ i o t).
Proof.
  intros x y [Rxy [? Hxy]].
  exists Rxy; ssplit; [ assumption | ].
  cbn [circuit_state step]. intros; logical_simplify.
  pose proof (fun i => proj1 (Hxy _ _ i ltac:(eassumption))) as Hxy1.
  pose proof (fun i => proj2 (Hxy _ _ i ltac:(eassumption))) as Hxy2.
  clear Hxy. logical_simplify. repeat (destruct_pair_let; cbn [fst snd]).
  rewrite Hxy1. ssplit; eauto.
Qed.

(* r1 = r2 -> cequivn c1 c2 -> cequivn (LoopInit r1 c1) (LoopInit r2 c2) *)
Global Instance Proper_LoopInit {i s o} :
  Proper (eq ==> cequivn ==> cequivn) (@LoopInit _ _ i o s).
Proof.
  cbv [LoopInit]. simpl_ident. repeat intro; subst.
  lazymatch goal with H : cequivn _ _ |- _ => rewrite H end.
  reflexivity.
Qed.

(* cequivn c1 c2 -> cequivn (LoopCE c1) (LoopCE c2) *)
Global Instance Proper_LoopCE {i s o} :
  Proper (cequivn ==> cequivn) (@LoopCE _ _ i o s).
Proof. apply Proper_LoopInitCE. reflexivity. Qed.

(* cequivn c1 c2 -> cequivn (Loop c1) (Loop c2) *)
Global Instance Proper_Loop {i s o} :
  Proper (cequivn ==> cequivn) (@Loop _ _ i o s).
Proof. apply Proper_LoopInit. reflexivity. Qed.
