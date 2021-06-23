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
Require Import Cava.Semantics.Simulation.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.

(* Circuit equivalence relation *)
Definition cequiv {i o} (c1 c2 : Circuit i o) : Prop :=
  (* there exists some relation between the circuit states... *)
  exists (R : value (circuit_state c1) -> value (circuit_state c2) -> Prop),
    (* ...and the relation holds on the reset states *)
    R (reset_state c1) (reset_state c2)
    (* ...and if the relation holds, stepping each circuit on the same input
         results in the same output as well as new states on which the relation
         continues to hold *)
    /\ (forall s1 s2 input,
          R s1 s2 ->
          snd (step c1 s1 input) = snd (step c2 s2 input)
          /\ R (fst (step c1 s1 input)) (fst (step c2 s2 input))).

(* cequiv is transitive *)
Global Instance Transitive_cequiv {i o} : Transitive (@cequiv i o) | 10.
Proof.
  intros x y z [Rxy [? Hxy]] [Ryz [? Hyz]]. logical_simplify.
  exists (fun (st1 : value (circuit_state x)) (st2 : value (circuit_state z)) =>
       exists st3 : value (circuit_state y), Rxy st1 st3 /\ Ryz st3 st2).
  ssplit; [ exists (reset_state y); tauto | ].
  intros; logical_simplify.
  specialize (Hxy _ _ ltac:(eassumption) ltac:(eassumption)).
  specialize (Hyz _ _ ltac:(eassumption) ltac:(eassumption)).
  logical_simplify. ssplit; [ congruence | ]. eauto.
Qed.

(* cequiv is reflexive *)
Global Instance Reflexive_cequiv {i o} : Reflexive (@cequiv i o) | 10.
Proof.
  repeat intro. exists eq. ssplit; [ reflexivity | ].
  intros; subst. ssplit; reflexivity.
Qed.

(* cequiv is symmetric *)
Global Instance Symmetric_cequiv {i o} : Symmetric (@cequiv i o) | 10.
Proof.
  intros x y [R [? HR]]. logical_simplify.
  exists (fun st1 st2 => R st2 st1). ssplit; [ assumption | ].
  intros. specialize (HR _ _ ltac:(eassumption) ltac:(eassumption)).
  logical_simplify. eauto.
Qed.

(* cequiv is an equivalence relation *)
Global Instance Equivalence_cequiv {i o} : Equivalence (@cequiv i o) | 10.
Proof. constructor; typeclasses eauto. Qed.

(* equivalent circuits produce the same output on the same input *)
Lemma simulate_cequiv {i o} (c1 c2 : Circuit i o) :
  cequiv c1 c2 -> forall input, simulate c1 input = simulate c2 input.
Proof.
  intros [R ?]; intros. logical_simplify. cbv [simulate].
  eapply fold_left_accumulate_double_invariant_In
    with (I:=fun st1 st2 acc1 acc2 =>
               R st1 st2 /\ acc1 = acc2).
  { ssplit; eauto. }
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

(* Proper instance allows rewriting under simulate *)
Global Instance Proper_simulate i o :
  Proper (cequiv ==> eq ==> eq) (@simulate i o).
Proof. repeat intro; subst. apply simulate_cequiv; auto. Qed.

(* r1 = r2 -> cequiv c1 c2 -> cequiv (LoopInitCE r1 c1) (LoopInitCE r2 c2) *)
Global Instance Proper_LoopInitCE {i s o} :
  Proper (eq ==> cequiv ==> cequiv) (@LoopInitCE _ _ i o s).
Proof.
  repeat intro; subst.
  lazymatch goal with H : cequiv _ _ |- _ => destruct H as [R ?] end.
  logical_simplify.
  exists (fun st1 st2 => R (fst st1) (fst st2) /\ snd st1 = snd st2).
  cbn [reset_state circuit_state fst snd] in *.
  ssplit; [ solve [auto] .. | ]. intros; logical_simplify.
  cbn [value] in *. destruct_products; cbn [fst snd] in *; subst.
  cbn [step]. simpl_ident.
  repeat destruct_pair_let; cbn [fst snd]. cbn [value]. fold @value combType.
  lazymatch goal with
  | H : forall _ _ _, R _ _ -> _ /\ _, HR : R _ _ |- context [step _ _ ?i] =>
  let H1 := fresh in
  let H2 := fresh in
  specialize (H _ _ i HR); destruct H as [H1 H2];
    rewrite ?H1, ?H2
  end.
  ssplit; eauto.
Qed.

(* cequiv c1 c3 -> cequiv c2 c4 -> cequiv (c1 >==> c2) (c3 >==> c4) *)
Global Instance Proper_Compose {i t o} :
  Proper (cequiv ==> cequiv ==> cequiv) (@Compose _ _ i t o).
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
  rewrite ?Hab1, ?Hcd1.
  ssplit; eauto; [ apply Hab2 | apply Hcd2 ].
Qed.

(* cequiv c1 c2 -> cequiv (First c1) (First c2) *)
Global Instance Proper_First {i o t} :
  Proper (cequiv ==> cequiv) (@First _ _ i o t).
Proof.
  intros x y [Rxy [? Hxy]].
  exists Rxy; ssplit; [ assumption | ].
  cbn [circuit_state step]. intros; logical_simplify.
  pose proof (fun i => proj1 (Hxy _ _ i ltac:(eassumption))) as Hxy1.
  pose proof (fun i => proj2 (Hxy _ _ i ltac:(eassumption))) as Hxy2.
  clear Hxy. logical_simplify. repeat (destruct_pair_let; cbn [fst snd]).
  rewrite Hxy1. ssplit; eauto.
Qed.

(* cequiv c1 c2 -> cequiv (Second c1) (Second c2) *)
Global Instance Proper_Second {i o t} :
  Proper (cequiv ==> cequiv) (@Second _ _ i o t).
Proof.
  intros x y [Rxy [? Hxy]].
  exists Rxy; ssplit; [ assumption | ].
  cbn [circuit_state step]. intros; logical_simplify.
  pose proof (fun i => proj1 (Hxy _ _ i ltac:(eassumption))) as Hxy1.
  pose proof (fun i => proj2 (Hxy _ _ i ltac:(eassumption))) as Hxy2.
  clear Hxy. logical_simplify. repeat (destruct_pair_let; cbn [fst snd]).
  rewrite Hxy1. ssplit; eauto.
Qed.

(* r1 = r2 -> cequiv c1 c2 -> cequiv (LoopInit r1 c1) (LoopInit r2 c2) *)
Global Instance Proper_LoopInit {i s o} :
  Proper (eq ==> cequiv ==> cequiv) (@LoopInit _ _ i o s).
Proof.
  cbv [LoopInit]. simpl_ident. repeat intro; subst.
  lazymatch goal with H : cequiv _ _ |- _ => rewrite H end.
  reflexivity.
Qed.

(* cequiv c1 c2 -> cequiv (LoopCE c1) (LoopCE c2) *)
Global Instance Proper_LoopCE {i s o} :
  Proper (cequiv ==> cequiv) (@LoopCE _ _ i o s).
Proof. apply Proper_LoopInitCE. reflexivity. Qed.

(* cequiv c1 c2 -> cequiv (Loop c1) (Loop c2) *)
Global Instance Proper_Loop {i s o} :
  Proper (cequiv ==> cequiv) (@Loop _ _ i o s).
Proof. apply Proper_LoopInit. reflexivity. Qed.
