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
  (* there exists some relation between the circuits' internal states... *)
  exists (R : value (circuit_state c1) -> value (circuit_state c2) -> Prop),
    (* ...and the reset states are related *)
    R (reset_state c1) (reset_state c2)
    (* ...and if the states are related, stepping each circuit on the same input
         results in the same output as well as new related states *)
    /\ (forall s1 s2 input,
          R s1 s2 ->
          snd (step c1 s1 input) = snd (step c2 s2 input)
          /\ R (fst (step c1 s1 input)) (fst (step c2 s2 input))).

(* TODO: move? *)
Lemma ex_split_pair {A B} (P : A * B -> Prop) :
  (exists a b, P (a,b)) -> (exists ab, P ab).
Proof. intros. logical_simplify. eexists; eauto. Qed.

(* TODO: move? *)
Ltac eexists_destruct :=
  repeat lazymatch goal with
         | |- exists _ : (_ * _)%type, _ => apply ex_split_pair
         | |- exists _ : unit, _ => exists tt
         | |- exists _, _ => eexists
         end.

(* find the hypothesis saying circuit state equivalence is preserved over
   [step], and specialize it to the current arguments *)
Local Ltac use_preserved :=
  lazymatch goal with
  | H : (forall _ _ _, ?R _ _ -> _ /\ _), HR : ?R ?s1 ?s2
    |- context [step _ ?s1 ?i] =>
    let H1 := fresh in
    let H2 := fresh in
    specialize (H s1 s2 i HR); destruct H as [H1 H2];
    rewrite ?H1, ?H2
end.

(* cequiv is transitive *)
Global Instance Transitive_cequiv {i o} : Transitive (@cequiv i o) | 10.
Proof.
  intros x y z [Rxy [? Hxy]] [Ryz [? Hyz]].
  logical_simplify. exists (fun x z => exists y, Rxy x y /\ Ryz y z).
  ssplit; [ solve [eauto] | ].
  intros; logical_simplify; subst.
  repeat use_preserved. ssplit; eauto.
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
  intros x y [Rxy [? Hxy]]. logical_simplify. exists (fun y x => Rxy x y).
  ssplit; [ solve [eauto] | ].
  intros; logical_simplify; subst.
  repeat use_preserved. ssplit; eauto.
Qed.

(* cequiv is an equivalence relation *)
Global Instance Equivalence_cequiv {i o} : Equivalence (@cequiv i o) | 10.
Proof. constructor; typeclasses eauto. Qed.

(* Try to solve [Proper] goals with cequiv *)
Local Ltac proper_hammer :=
  cbn [reset_state circuit_state fst snd value] in *; fold @value combType in *;
  ssplit; intros; destruct_products; cbn [fst snd] in *;
    [ solve [eauto] .. | ];
  cbn [circuit_state step fst snd]; intros; logical_simplify; subst;
  cbn [value]; fold @value combType in *;
  repeat use_preserved; ssplit; try congruence.

(* equivalent circuits produce the same output on the same input *)
Lemma simulate_cequiv {i o} (c1 c2 : Circuit i o) :
  cequiv c1 c2 -> forall input, simulate c1 input = simulate c2 input.
Proof.
  intros [R ?]; intros. logical_simplify. cbv [simulate].
  eapply fold_left_accumulate_double_invariant_In
    with (I:=fun st1 st2 acc1 acc2 =>
               R st1 st2 /\ acc1 = acc2).
  { ssplit; eauto. }
  { intros; logical_simplify; subst. use_preserved.
    ssplit; congruence. }
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
  exists (fun s1 s2 => R (fst s1) (fst s2) /\ snd s1 = snd s2).
  proper_hammer.
Qed.

(* cequiv c1 c3 -> cequiv c2 c4 -> cequiv (c1 >==> c2) (c3 >==> c4) *)
Global Instance Proper_Compose {i t o} :
  Proper (cequiv ==> cequiv ==> cequiv) (@Compose _ _ i t o).
Proof.
  intros a b [Rab ?] c d [Rcd ?].
  exists (fun ac bd => Rab (fst ac) (fst bd) /\ Rcd (snd ac) (snd bd)).
  proper_hammer.
Qed.

(* cequiv c1 c2 -> cequiv (First c1) (First c2) *)
Global Instance Proper_First {i o t} :
  Proper (cequiv ==> cequiv) (@First _ _ i o t).
Proof. intros x y [R ?]. exists R. proper_hammer. Qed.

(* cequiv c1 c2 -> cequiv (Second c1) (Second c2) *)
Global Instance Proper_Second {i o t} :
  Proper (cequiv ==> cequiv) (@Second _ _ i o t).
Proof. intros x y [R ?]. exists R. proper_hammer. Qed.

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
