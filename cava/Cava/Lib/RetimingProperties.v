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
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Loopless.
Require Import Cava.Semantics.LooplessProperties.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Semantics.WeakEquivalence.
Require Import Cava.Lib.CircuitTransforms.
Require Import Cava.Lib.CircuitTransformsProperties.
Require Import Cava.Lib.Retiming.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Import ListNotations Circuit.Notations MonadNotation.

Lemma split_delay_init {t1 t2} (r1 : value t1) (r2 : value t2) :
  cequiv (DelayInit (t:=t1*t2) (r1, r2)) (Par (DelayInit r1) (DelayInit r2)).
Proof.
  exists eq. ssplit; [ reflexivity | ].
  cbn [value circuit_state Par].
  intros; subst; destruct_products. ssplit; reflexivity.
Qed.
Lemma split_delay {t1 t2} : cequiv (Delay (t:=t1*t2)) (Par Delay Delay).
Proof. apply split_delay_init. Qed.

Lemma LoopInit_Compose_l {i o s t}
      (c : Circuit t i) (body : Circuit (i * s) (o * s)) r :
  cequiv (c >==> LoopInit r body) (LoopInit r (First c >==> body)).
Proof.
  exists (fun (s1 : value (circuit_state c)
             * (unit * (value (circuit_state body) * value s)))
       (s2 : unit * (value (circuit_state c) * value (circuit_state body)
                     * value s)) =>
       let '(c1,(_,(b1,v1))) := s1 in
       let '(_,(c2,b2,v2)) := s2 in
       c1 = c2 /\ b1 = b2 /\ v1 = v2).
  cbn [reset_state circuit_state value LoopInit].
  ssplit; [ reflexivity .. | ].
  intros; destruct_products; subst.
  cbn [step fst snd LoopInit]. simpl_ident.
  ssplit; reflexivity.
Qed.

Lemma LoopInit_ignore_input {t s} r (c : Circuit s s) :
  cequiv (LoopInit r (Second c)) (Id (t:=t)).
Proof.
  exists (fun _ _ => True). ssplit; [ tauto | ].
  cbn [LoopInit circuit_state value Id].
  intros; destruct_products; cbn [fst snd] in *. logical_simplify.
  cbn [step LoopInit Id fst snd]. ssplit; auto.
Qed.
Hint Rewrite @LoopInit_ignore_input using solve [eauto] : circuitsimpl.

Lemma LoopInit_Par {i o s} (c1 : Circuit i o) (c2 : Circuit s s) r :
  cequiv (LoopInit r (Par c1 c2)) c1.
Proof.
  cbv [Par]. rewrite First_Second_comm, LoopInit_First_r.
  autorewrite with circuitsimpl; reflexivity.
Qed.
Hint Rewrite @LoopInit_Par using solve [eauto] : circuitsimpl.

Lemma move_delay_init {i o} (c : Circuit i o) r :
  cequiv (DelayInit r >==> c)
         (chreset c (fst (step c (reset_state c) r))
                  >==> DelayInit (snd (step c (reset_state c) r))).
Proof.
  exists (fun (s1 : value i * value (circuit_state c))
       (s2 : value (circuit_state (chreset c _)) * value o) =>
       step c (snd s1) (fst s1) = (from_chreset_state (fst s2), snd s2)).
  cbn [fst snd reset_state from_chreset_state reset_state chreset
           circuit_state value].
  rewrite chreset_reset, from_to_chreset_state.
  rewrite <-surjective_pairing.
  ssplit; [ reflexivity | ].
  intros; destruct_products. cbn [step fst snd] in *.
  lazymatch goal with H : step _ _ _ = _ |- _ => rewrite H end.
  ssplit; [ reflexivity | ]. cbn [fst snd].
  rewrite step_chreset; cbn [fst snd].
  rewrite from_to_chreset_state.
  rewrite <-surjective_pairing.
  reflexivity.
Qed.

Lemma move_delay {i o} (c : Circuit i o) :
  cequiv (Delay >==> c)
         (chreset c (fst (step c (reset_state c) defaultValue))
                  >==> DelayInit (snd (step c (reset_state c) defaultValue))).
Proof. apply move_delay_init. Qed.

Lemma split_ndelays {t1 t2} n :
  cequiv (ndelays (t1*t2) n) (Par (ndelays t1 n) (ndelays t2 n)).
Proof.
  induction n; cbn [ndelays]; autorewrite with circuitsimpl; [ reflexivity | ].
  rewrite split_delay, IHn. cbv [Par]. autorewrite with circuitsimpl.
  eapply Proper_Compose; [ | reflexivity ].
  rewrite <-(Compose_assoc (First _) (Second _) (First _)).
  rewrite <-!First_Second_comm. autorewrite with circuitsimpl.
  reflexivity.
Qed.

Lemma Par_Id_l {i o t} (f : Circuit i o) : cequiv (Par f (Id (t:=t))) (First f).
Proof. cbv [Par]. autorewrite with circuitsimpl. reflexivity. Qed.
Hint Rewrite @Par_Id_l using solve [eauto] : circuitsimpl.

Lemma Par_Id_r {i o t} (f : Circuit i o) : cequiv (Par (Id (t:=t)) f) (Second f).
Proof. cbv [Par]. autorewrite with circuitsimpl. reflexivity. Qed.
Hint Rewrite @Par_Id_r using solve [eauto] : circuitsimpl.

Lemma Second_Comb {i o t} f :
  cequiv (Second (Comb f)) (Comb (i:=t*i) (o:=t*o) (fun x => (fst x, f (snd x)))).
Proof.
  exists (fun _ _ => True). cbn [value circuit_state]. ssplit; [ tauto | ].
  intros; logical_simplify. cbn [step fst snd]. ssplit; tauto.
Qed.
Hint Rewrite @Second_Comb using solve [eauto] : pull_comb.

Lemma First_Comb {i o t} f :
  cequiv (First (Comb f)) (Comb (i:=i*t) (o:=o*t) (fun x => (f (fst x), snd x))).
Proof.
  exists (fun _ _ => True). cbn [value circuit_state]. ssplit; [ tauto | ].
  intros; logical_simplify. cbn [step fst snd]. ssplit; tauto.
Qed.
Hint Rewrite @First_Comb using solve [eauto] : pull_comb.

Lemma Compose_Comb {i t o} f g :
  cequiv (@Compose _ _ i t o (Comb f) (Comb g)) (Comb (f >=> g)).
Proof.
  exists (fun _ _ => True). cbn [value circuit_state]. ssplit; [ tauto | ].
  intros; logical_simplify. cbn [step fst snd]. ssplit; tauto.
Qed.
Hint Rewrite @Compose_Comb using solve [eauto] : pull_comb.

Lemma Compose_Comb_r {i t1 t2 o} c f g :
  cequiv (@Compose _ _ i t2 o (@Compose _ _ i t1 t2 c (Comb f)) (Comb g))
         (c >==> Comb (f >=> g)).
Proof.
  rewrite <-Compose_Comb. autorewrite with circuitsimpl. reflexivity.
Qed.
Hint Rewrite @Compose_Comb_r using solve [eauto] : pull_comb.

Lemma loopless_loop_free {i o} (c : Circuit i o) :
  is_loop_free c = true -> cequiv (loopless c) (First c).
Proof.
  induction c; cbn [loopless is_loop_free];
    rewrite ?Bool.andb_true_iff; intros; logical_simplify.
  { (* Comb *)
    reflexivity. }
  { (* Compose *)
    rewrite IHc1, IHc2 by auto.
    exists (fun (s1 : unit * value (circuit_state c1) * unit * value (circuit_state c2) * unit)
         (s2 : value (circuit_state c1) * value (circuit_state c2)) =>
         s1 = (tt, fst s2, tt, snd s2, tt)).
    cbn [value circuit_state reset_state loops_state fst snd].
    ssplit; [ reflexivity | ].
    intros; subst; destruct_products; cbn [fst snd step].
    ssplit; reflexivity. }
  { (* First *)
    rewrite IHc by auto.
    exists (fun (s1 : unit * value (circuit_state c) * unit) (s2: value (circuit_state c)) =>
         s1 = (tt, s2, tt)).
    cbn [value circuit_state reset_state loops_state fst snd].
    ssplit; [ reflexivity | ].
    intros; subst; destruct_products; cbn [fst snd step].
    ssplit; reflexivity. }
  { (* Second *)
    rewrite IHc by auto.
    exists (fun (s1 : unit * value (circuit_state c) * unit) (s2: value (circuit_state c)) =>
         s1 = (tt, s2, tt)).
    cbn [value circuit_state reset_state loops_state fst snd].
    ssplit; [ reflexivity | ].
    intros; subst; destruct_products; cbn [fst snd step].
    ssplit; reflexivity. }
  { (* Loop *)
    discriminate. }
  { (* Delay *)
    reflexivity. }
Qed.

Axiom reassemble_state :
  forall {i o} (c : Circuit i o), value (circuit_state (loopless c)) -> value (loops_state c) -> value (circuit_state c).

Axiom loops_state_from_circuit_state :
  forall {i o} (c : Circuit i o), value (circuit_state c) -> value (loops_state c).
Axiom loopless_state_from_circuit_state :
  forall {i o} (c : Circuit i o), value (circuit_state c) -> value (circuit_state (loopless c)).

Axiom to_chreset_loops_state :
  forall {i o} {c : Circuit i o} {r : value (circuit_state c)}, value (loops_state c) -> value (loops_state (chreset c r)).
Axiom from_chreset_loops_state :
  forall {i o} {c : Circuit i o} {r : value (circuit_state c)}, value (loops_state (chreset c r)) -> value (loops_state c).

Lemma ndelays_succ_l {t} n : cequiv (ndelays t (S n)) (Delay >==> ndelays t n).
Proof.
  induction n; cbn [ndelays]; autorewrite with circuitsimpl; [ reflexivity | ].
  rewrite <-IHn. reflexivity.
Qed.

Lemma simulate_retimed {i o} (c1 c2 : Circuit i o) n :
  retimed n c1 c2 ->
  forall input1 input2 : list (value i),
    length input1 = length input2 * (n + 1) ->
    (forall t, nth t input2 defaultValue = nth (t*(n+1)) input1 defaultValue) ->
    forall t,
      nth t (simulate c2 input2) defaultValue
      = nth (t*(n+1) + n) (simulate c1 input1) defaultValue.
Proof.
  intros [r Hr]. intros.
  (* immediately handle case where t is out of bounds *)
  destr (t <? length input2);
    [ | rewrite !nth_overflow by (autorewrite with push_length; nia);
        reflexivity ].
  erewrite (simulate_cequiv c1) by eauto.
  cbv [simulate]. cbn [reset_state LoopInit Par mealy].
  rewrite !chreset_reset.
  cbn [step LoopInit Par fst snd mealy]. simpl_ident.
  cbv [Combinators.swap]. simpl_ident. fold @circuit_state.
  (*
  rewrite step_chreset.
  rewrite fold_left_accumulate_to_seq with (ls:=input2) (default:=defaultValue).
  erewrite !nth_fold_left_accumulate by nia.*)
  
  (* separate input1 into (length input2) lists of multiple inputs, prove that
     executing each list is equivalent to one execution of c2 *)
Admitted.

Fixpoint Forall_ndelays {t1 t2 n} (R : value t1 -> value t2 -> Prop)
  : value (circuit_state (ndelays t1 n))
    -> value (circuit_state (ndelays t2 n)) -> Prop :=
  match n with
  | 0 => fun _ _ => True
  | S _ =>
    fun d1 d2 =>
      Forall_ndelays R (fst d1) (fst d2) /\ R (snd d1) (snd d2)
  end.

Lemma Forall_ndelays_to_ndelays_state
      {t1 t2 n} (R : value t1 -> value t2 -> Prop) x1 x2 :
  R x1 x2 -> Forall_ndelays (n:=n) R (to_ndelays_state x1) (to_ndelays_state x2).
Proof. induction n; intros; cbn [Forall_ndelays]; ssplit; auto. Qed.

Lemma Forall_ndelays_step {n} t1 t2 (R : value t1 -> value t2 -> Prop)
      x1 x2 y1 y2 :
  Forall_ndelays R x1 x2 -> R y1 y2 ->
  (Forall_ndelays R (fst (step (ndelays t1 n) x1 y1))
                  (fst (step (ndelays t2 n) x2 y2))
   /\ R (snd (step (ndelays t1 n) x1 y1))
       (snd (step (ndelays t2 n) x2 y2))).
Proof.
  induction n; intros; cbn [Forall_ndelays] in *; [ tauto | ].
  cbn [ndelays circuit_state value] in *. destruct_products.
  cbn [step Delay fst snd] in *. split; auto.
Qed.

Lemma Forall_ndelays_step_out {n} t1 t2 (R : value t1 -> value t2 -> Prop)
      x1 x2 y1 y2 :
  Forall_ndelays R x1 x2 -> R y1 y2 ->
  R (snd (step (ndelays t1 n) x1 y1))
       (snd (step (ndelays t2 n) x2 y2)).
Proof. apply Forall_ndelays_step. Qed.

Lemma Forall_ndelays_step_state {n} t1 t2 (R : value t1 -> value t2 -> Prop)
      x1 x2 y1 y2 :
  Forall_ndelays R x1 x2 -> R y1 y2 ->
  Forall_ndelays R (fst (step (ndelays t1 n) x1 y1))
                  (fst (step (ndelays t2 n) x2 y2)).
Proof. apply Forall_ndelays_step. Qed.

Lemma step_mealy {i o} (c : Circuit i o)
      (s : value (circuit_state c)) (x : value i) (u : unit) :
  step (mealy c) u (x,s) = (tt, (snd (step c s x), fst (step c s x))).
Proof. cbn. cbv [Combinators.swap]. destruct_pair_let. reflexivity. Qed.

(* Helper for Proper_retimed *)
Lemma cequiv_mealy_loop_ndelays {i o} (c d : Circuit i o) n rvals :
  cequiv c d ->
  cequiv
    (LoopInit (reset_state c)
       (mealy c >==>
        Par (chreset (ndelays o n) rvals)
        (chreset (ndelays (circuit_state c) n)
                 (to_ndelays_state (reset_state c)))))
    (LoopInit (reset_state d)
              (mealy d >==>
                     Par (chreset (ndelays o n) rvals)
                     (chreset (ndelays (circuit_state d) n)
                              (to_ndelays_state (reset_state d))))).
Proof.
  cbv [retimed]. intros [Rcd [? Hcd_preserved]]. logical_simplify.
  exists (fun (s1 : unit
             * (unit
                * (value (circuit_state (chreset (ndelays o n) _))
                   * value (circuit_state (chreset (ndelays (circuit_state c) n) _)))
                * value (circuit_state c)))
       (s2 : unit
             * (unit
                * (value (circuit_state (chreset (ndelays o n) _)) *
                   value (circuit_state (chreset (ndelays (circuit_state d) n) _)))
                * value (circuit_state d))) =>
       let '(_,(_,(x1,y1),z1)) := s1 in
       let '(_,(_,(x2,y2),z2)) := s2 in
       from_chreset_state x1 = from_chreset_state x2
       /\ Forall_ndelays Rcd (from_chreset_state y1) (from_chreset_state y2)
       /\ Rcd z1 z2).
  ssplit; intros.
  { cbn [LoopInit Par reset_state].
    rewrite !chreset_reset, !from_to_chreset_state.
    ssplit; [ reflexivity | | assumption ].
    apply Forall_ndelays_to_ndelays_state; auto. }
  { cbn [value circuit_state LoopInit Par] in *.
    destruct_products. logical_simplify.
    cbn [LoopInit Par reset_state step fst snd].
    simpl_ident. rewrite !step_chreset, !step_mealy.
    cbn [fst snd]. rewrite !from_to_chreset_state.
    lazymatch goal with
    | H : from_chreset_state _ = from_chreset_state _ |- _ => rewrite H
    end.
    specialize (Hcd_preserved _ _ ltac:(eassumption) ltac:(eassumption)).
    destruct Hcd_preserved as [Hcd_preserved0 Hcd_preserved1].
    rewrite Hcd_preserved0. ssplit; [ reflexivity .. | | ].
    { apply Forall_ndelays_step_state; auto. }
    { apply Forall_ndelays_step_out; auto. } }
Qed.

(* TODO: the definition of cequiv might need to change to make this provable; in
   particular, the loop and non-loop states need to be able to vary
   independently *)
Instance Proper_retimed {i o} n :
  Proper (cequiv ==> cequiv ==> iff) (@retimed i o n).
Proof.
  intros a b Hab c d Hcd. split.
  { cbv [retimed]. intros [rvals Hac]. exists rvals.
    rewrite <-Hab, Hac. apply cequiv_mealy_loop_ndelays; auto. }
  { cbv [retimed]. intros [rvals Hbd]. exists rvals.
    rewrite Hab, Hbd. apply cequiv_mealy_loop_ndelays;
                        symmetry; auto. }
Qed.

Lemma cequiv_mealy {i o} (c : Circuit i o) :
  cequiv c (LoopInit (reset_state c) (mealy c)).
Proof.
  exists (fun s1 s2 => s2 = (tt, (tt, s1))).
  ssplit; [ reflexivity | ].
  cbn [circuit_state value LoopInit step fst snd].
  intros; destruct_products. logical_simplify. simpl_ident.
  rewrite !step_mealy. cbn [fst snd]. ssplit; reflexivity.
Qed.

Fixpoint append_ndelays {t n m}
  : value (circuit_state (ndelays t n)) ->
    value (circuit_state (ndelays t m)) ->
    value (circuit_state (ndelays t (n + m))) :=
  match n with
  | O => fun x1 x2 => x2
  | S _ => fun x1 x2 => (append_ndelays (fst x1) x2, snd x1)
  end.
Fixpoint split1_ndelays {t n m}
  : value (circuit_state (ndelays t (n + m))) ->
    value (circuit_state (ndelays t n)) :=
  match n with
  | O => fun _ => tt
  | S _ => fun x => (split1_ndelays (fst x), snd x)
  end.
Fixpoint split2_ndelays {t n m}
  : value (circuit_state (ndelays t (n + m))) ->
    value (circuit_state (ndelays t m)) :=
  match n with
  | O => fun x => x
  | S _ => fun x => split2_ndelays (fst x)
  end.


Fixpoint combine_ndelays {t1 t2 n}
  : value (circuit_state (ndelays t1 n)) ->
    value (circuit_state (ndelays t2 n)) ->
    value (circuit_state (ndelays (t1 * t2) n)) :=
  match n with
  | O => fun _ _ => tt
  | S _ => fun x1 x2 => (combine_ndelays (fst x1) (fst x2), (snd x1, snd x2))
  end.

Fixpoint map_ndelays {t1 t2 n} (f : value t1 -> value t2)
  : value (circuit_state (ndelays t1 n))
    -> value (circuit_state (ndelays t2 n)) :=
  match n with
  | 0 => fun x => x
  | S _ => fun x => (map_ndelays f (fst x), f (snd x))
  end.

Lemma LoopInit_delay_feedback {i o s1 s2}
      (f1 : value (i * s1) -> cava (value (o * s1)))
      (f2 : value (i * s2) -> cava (value (o * s2)))
      r1 r2 n :
  cequiv (LoopInit r1 (Comb f1)) (LoopInit r2 (Comb f2)) ->
  cequiv (LoopInit r1 ((Comb f1)
                         >==> Second (chreset (ndelays s1 n)
                                              (to_ndelays_state r1))))
         (LoopInit r2 ((Comb f2)
                         >==> Second (chreset (ndelays s2 n)
                                              (to_ndelays_state r2)))).
Proof.
  intros [R [? HR]]. cbn [value circuit_state LoopInit] in *.
  exists (fun (s1 : unit
             * (unit
                * value (circuit_state (chreset (ndelays s1 n) _))
                * value s1))
       (s2 : unit
             * (unit
                * value (circuit_state (chreset (ndelays s2 n) _))
                * value s2)) =>
       let '(_,(_,d1,l1)) := s1 in
       let '(_,(_,d2,l2)) := s2 in
       Forall_ndelays
         (fun x1 x2 => R (tt, (tt, x1)) (tt, (tt, x2)))
         (from_chreset_state d1)
         (from_chreset_state d2)
       /\ R (tt, (tt, l1)) (tt, (tt, l2))).
  cbn [reset_state circuit_state value LoopInit] in *.
  rewrite !chreset_reset, !from_to_chreset_state.
  ssplit; intros; destruct_products;
    [ solve [auto using Forall_ndelays_to_ndelays_state] .. | ].
  cbn [step LoopInit fst snd] in *. simpl_ident.
  rewrite !step_chreset. cbn [fst snd].
  rewrite !from_to_chreset_state.
  specialize (HR _ _ ltac:(eassumption) ltac:(eassumption)).
  cbn in HR. rewrite (proj1 HR). logical_simplify.
  ssplit; [ reflexivity | | ].
  { eapply Forall_ndelays_step_state; eauto. }
  { eapply Forall_ndelays_step_out
      with (R0:=(fun (x1 : value s1) (x2 : value s2) => R (tt, (tt, x1)) (tt, (tt, x2))));
    eauto. }
Qed.

Lemma LoopInit_delay_body {i o s1 s2}
      (f1 : value (i * s1) -> cava (value (o * s1)))
      (f2 : value (i * s2) -> cava (value (o * s2)))
      r1 r2 n v :
  cequiv (LoopInit r1 (Comb f1)) (LoopInit r2 (Comb f2)) ->
  cequiv (LoopInit r1 (Comb f1 >==> (Par (chreset (ndelays o n) v)
                                         (chreset (ndelays s1 n)
                                                  (to_ndelays_state r1)))))
         (LoopInit r2 (Comb f2 >==> (Par (chreset (ndelays o n) v)
                                         (chreset (ndelays s2 n)
                                                  (to_ndelays_state r2))))).
Proof.
  intros. cbv [Par].
  rewrite !First_Second_comm, !Compose_assoc.
  rewrite !LoopInit_First_r.
  erewrite LoopInit_delay_feedback by eassumption.
  reflexivity.
Qed.

Lemma cequiv_append_ndelays t n m r1 r2 :
  cequiv (chreset (ndelays t (n + m)) (append_ndelays r1 r2))
         (chreset (ndelays t m) r2 >==> chreset (ndelays t n) r1).
Proof.
  revert m r1 r2.
  induction n; intros;
    cbn [Nat.add chreset ndelays append_ndelays fst snd];
    autorewrite with circuitsimpl; [ reflexivity | ].
  rewrite IHn. reflexivity.
Qed.

Lemma to_ndelays_state_append t n m r :
  @to_ndelays_state t (n+m) r = append_ndelays (to_ndelays_state r)
                                               (to_ndelays_state r).
Proof.
  revert m r; induction n; intros;
    cbn [Nat.add to_ndelays_state append_ndelays fst snd];
    [ reflexivity | ].
  rewrite IHn; reflexivity.
Qed.

Lemma Par_Compose {i1 i2 t1 t2 o1 o2}
      (A : Circuit i1 t1) (B : Circuit t1 o1)
      (C : Circuit i2 t2) (D : Circuit t2 o2) :
  cequiv (Par (A >==> B) (C >==> D)) (Par A C >==> Par B D).
Proof.
  cbv [Par]. autorewrite with circuitsimpl.
  apply Proper_Compose; [ | reflexivity ].
  rewrite <-!Compose_assoc.
  apply Proper_Compose; [ reflexivity | ].
  rewrite First_Second_comm; reflexivity.
Qed.

Fixpoint is_combinational {i o} (c : Circuit i o) : bool :=
  match c with
  | Comb _ => true
  | Compose f g => (is_combinational f && is_combinational g)%bool
  | First f => is_combinational f
  | Second f => is_combinational f
  | DelayInit r => false
  | LoopInitCE r body => false
  end.

(* the state of combinational circuits is trivial; any two state values are
   equal *)
Lemma is_combinational_state {i o} (c : Circuit i o) :
  is_combinational c = true -> forall (x y : value (circuit_state c)), x = y.
Proof.
  induction c; cbn [value circuit_state is_combinational];
    try discriminate; intros; destruct_products; logical_simplify;
    repeat lazymatch goal with
           | H : (_ && _)%bool = true |- _ =>
             apply Bool.andb_true_iff in H; logical_simplify
           | |- pair _ _ = pair _ _ => apply f_equal2
           | |- ?x = ?x => reflexivity
           | IH : is_combinational ?c = true -> (forall _ _, _ = _)
             |- @eq (value (circuit_state ?c)) _ _ => apply IH; assumption
           end.
Qed.

Local Ltac infer_combinational_states_equal :=
  repeat lazymatch goal with
         | H : is_combinational ?c = true,
               x : value (circuit_state ?c),
                   y : value (circuit_state ?c) |- _ =>
           pose proof (is_combinational_state c H x y); subst x
         end.

Lemma step_combinational {i o} (c : Circuit i o) s x :
  is_combinational c = true ->
  step c s x = (s, snd (step c s x)).
Proof.
  intros.
  rewrite (surjective_pairing (step c s x)). cbn [fst snd].
  f_equal. apply is_combinational_state; auto.
Qed.

Lemma is_combinational_mealy {i o} (c : Circuit i o) :
  is_combinational c = true ->
  cequiv (mealy c) (First c).
Proof.
  intros. exists (fun _ _ => True). split; [ tauto | ].
  cbn [value circuit_state mealy]. intros.
  split; [ | tauto ]. destruct_products; logical_simplify.
  infer_combinational_states_equal.
  rewrite step_mealy. cbn [step fst snd].
  f_equal; apply is_combinational_state; auto.
Qed.

Lemma combinational_to_mealy {i o} (c : Circuit i o) :
  is_combinational c = true ->
  cequiv c ((Comb (i:=i) (o:=i*circuit_state c)
                  (fun x => (x, defaultValue)))
              >==> mealy c
              >==> (Comb (i:=o*circuit_state c) (o:=o) fst)).
Proof.
  intros. exists (fun _ _ => True). split; [ tauto | ].
  cbn [value circuit_state mealy step fst snd]. intros.
  split; [ | tauto ]. destruct_products; logical_simplify.
  cbv [Combinators.swap]. simpl_ident. repeat destruct_pair_let.
  cbn [fst snd]. repeat (f_equal; [ ]).
  apply is_combinational_state; auto.
Qed.

Lemma retimed_delay_init_r {i o} (c1 c2 : Circuit i o) n r :
  is_combinational c2 = true ->
  retimed n c1 c2 ->
  retimed (S n) (c1 >==> DelayInit r) c2.
Proof.
  cbv [retimed]. cbn [Par circuit_state chreset value ndelays Id Delay].
  intros; logical_simplify.
  lazymatch goal with
  | d : value (circuit_state (ndelays o n)) |- _ => exists (d, r) end.
  cbn [fst snd to_ndelays_state].
  lazymatch goal with H : cequiv c1 _ |- _ => rewrite H; clear H end.
  rewrite is_combinational_mealy by auto.
  rewrite <-!LoopInit_Compose_l.
  rewrite <-(Compose_assoc c2 (LoopInit _ _) (DelayInit _)).
  apply Proper_Compose; [ reflexivity | ].
  autorewrite with circuitsimpl.
  reflexivity.
Qed.

Lemma retimed_delay_r {i o} (c1 c2 : Circuit i o) n :
  is_combinational c2 = true ->
  retimed n c1 c2 ->
  retimed (S n) (c1 >==> Delay) c2.
Proof. apply retimed_delay_init_r. Qed.

(* simulate a circuit to get an ndelays state *)
Fixpoint ndelays_value_from_sim {i o} (c : Circuit i o) {n}
  : value (circuit_state c) ->
    value (circuit_state (ndelays i n)) ->
    value (circuit_state (ndelays o n)) :=
  match n with
  | 0 => fun _ x => x
  | S m =>
    fun s x =>
      let so := step c s (snd x) in
      (ndelays_value_from_sim c (fst so) (fst x), snd so)
  end.

Lemma map_ndelays_to_ndelays_state {t1 t2} (f : value t1 -> value t2) n x :
  map_ndelays (n:=n) f (to_ndelays_state x) = to_ndelays_state (f x).
Proof.
  induction n; [ reflexivity | ].
  cbn [map_ndelays to_ndelays_state fst snd]. rewrite IHn.
  reflexivity.
Qed.

Lemma retimed_cequiv {i o} (c1 c2 : Circuit i o) :
  retimed 0 c1 c2 <-> cequiv c1 c2.
Proof.
  cbv [retimed]. cbn [ndelays Par circuit_state value chreset Id].
  split.
  { intros [? Heq]. rewrite Heq.
    autorewrite with circuitsimpl.
    rewrite <-cequiv_mealy. reflexivity. }
  { intros Heq. eexists_destruct.
    autorewrite with circuitsimpl.
    rewrite <-cequiv_mealy. auto. }
Qed.

Lemma LoopInit_change_state
      {i o s1 s2}
      (c1 : Circuit (i * s1) (o * s1))
      (c2 : Circuit (i * s2) (o * s2))
      (f : value s1 -> value s2) r :
  cequiv (c1 >==> Second (Comb f)) (Second (Comb f) >==> c2)->
  cequiv (LoopInit r c1) (LoopInit (f r) c2).
Proof.
  intros [R [Hreset Hpreserved]].
  exists (fun (x1 : unit * (value (circuit_state c1) * value s1))
       (x2 : unit * (value (circuit_state c2) * value s2)) =>
       let '(_,(y1,z1)) := x1 in
       let '(_,(y2,z2)) := x2 in
       R (y1,tt) (tt,y2) /\ f z1 = z2).
  cbn [value circuit_state reset_state LoopInit] in *.
  ssplit; [ solve [auto] .. | ].
  intros; destruct_products; logical_simplify. subst.
  cbn [step LoopInit fst snd] in *. simpl_ident.
  lazymatch goal with
  | H : R (?v, tt) _ |- context [step _ ?v] =>
    specialize (Hpreserved _ _ ltac:(apply pair; eassumption) H)
  end.
  cbn [fst snd] in Hpreserved. destruct Hpreserved as [Hout HR].
  fold @value in *. rewrite <-Hout. cbn [fst snd].
  ssplit; auto.
Qed.

Lemma mealy_compose_comb_r {i t o} (c1 : Circuit i t) (c2 : Circuit t o) :
  is_combinational c2 = true ->
  cequiv (mealy (c1 >==> c2))
         (Second (Comb (i:=_*circuit_state c2)
                       (fun x => fst x))
                 >==> mealy c1
                 >==> First c2
                 >==> Second (Comb (o:=_*circuit_state c2) (fun x => (x, defaultValue)))).
Proof.
  exists (fun _ _ => True). split; [ tauto | ].
  cbn [value circuit_state mealy]. intros; destruct_products.
  logical_simplify. infer_combinational_states_equal.
  cbn [step mealy fst snd]. cbv [Combinators.swap].
  simpl_ident. repeat destruct_pair_let; cbn [fst snd].
  ssplit; [ | tauto ].
  repeat lazymatch goal with |- (_,_) = (_,_) =>
                             apply f_equal2; try reflexivity; [ ] end.
  apply is_combinational_state; auto.
Qed.

Lemma mealy_compose_comb_l {i t o} (c1 : Circuit i t) (c2 : Circuit t o) :
  is_combinational c1 = true ->
  cequiv (mealy (c1 >==> c2))
         ((First c1)
            >==> Second (Comb (i:=circuit_state c1*_)
                              (fun x => snd x))
            >==> mealy c2
            >==> Second (Comb (o:=circuit_state c1*_) (fun x => (defaultValue,x)))).
Proof.
  exists (fun _ _ => True). split; [ tauto | ].
  cbn [value circuit_state mealy]. intros; destruct_products.
  logical_simplify. infer_combinational_states_equal.
  cbn [step mealy fst snd]. cbv [Combinators.swap].
  simpl_ident. repeat destruct_pair_let; cbn [fst snd].
  ssplit; [ | tauto ].
  repeat lazymatch goal with |- (_,_) = (_,_) =>
                             apply f_equal2; try reflexivity; [ ] end.
  apply is_combinational_state; auto.
Qed.

Lemma Comb_DelayInit_comm {i o} (c : Circuit i o) r :
  is_combinational c = true ->
  cequiv (DelayInit r >==> c)
         (c >==> DelayInit (snd (step c (reset_state c) r))).
Proof.
  exists (fun (s1 : value i * value (circuit_state c))
       (s2 : value (circuit_state c) * value o) =>
       step c (snd s1) (fst s1) = s2).
  cbn [reset_state circuit_state value step fst snd].
  split; [ apply step_combinational; assumption | ].
  intros; destruct_products. cbn [fst snd] in *.
  infer_combinational_states_equal.
  lazymatch goal with H : step _ _ _ = _ |- _ => rewrite H end.
  cbn [fst snd]. rewrite <-surjective_pairing.
  ssplit; reflexivity.
Qed.

Lemma Comb_ndelays_comm {i o} (c : Circuit i o) n r :
  is_combinational c = true ->
  cequiv (chreset (ndelays i n) r >==> c)
         (c >==> (chreset (ndelays o n)
                          (ndelays_value_from_sim c (reset_state c) r))).
Proof.
  revert c r; induction n; intros;
    [ cbn; autorewrite with circuitsimpl; reflexivity | ].
  cbn [ndelays chreset Delay]. autorewrite with circuitsimpl.
  cbn [ndelays_value_from_sim fst snd].
  rewrite <-(Compose_assoc (chreset (ndelays _ _) _) (DelayInit _) c).
  rewrite Comb_DelayInit_comm by auto.
  autorewrite with circuitsimpl. rewrite IHn by auto.
  rewrite step_combinational by auto. cbn [fst snd].
  repeat (apply Proper_Compose; try reflexivity; [ ]).
  rewrite step_combinational by auto.
  reflexivity.
Qed.

Lemma retimed_cancel_r {i t o} (c1 c2 : Circuit i t) (c3 : Circuit t o) n :
  is_combinational c3 = true ->
  retimed n c1 c2 ->
  retimed n (c1 >==> c3) (c2 >==> c3).
Proof.
  cbv [retimed]. intros; logical_simplify.
  exists (ndelays_value_from_sim c3 (reset_state c3) ltac:(eassumption)).
  lazymatch goal with H : cequiv c1 _ |- _ => rewrite H; clear H end.
  cbv [Par]; rewrite !First_Second_comm, !Compose_assoc.
  rewrite !LoopInit_First_r.
  rewrite <-(Compose_assoc (LoopInit _ _) _ c3).
  rewrite Comb_ndelays_comm by auto.
  autorewrite with circuitsimpl.
  apply Proper_Compose; [ | reflexivity ].
  rewrite <-LoopInit_First_r.
  erewrite (LoopInit_change_state (s1:=circuit_state c2 * circuit_state c3))
    with (f:=fst); [ reflexivity | ].
  rewrite mealy_compose_comb_r by auto.
  cbn [circuit_state reset_state].
  autorewrite with circuitsimpl.
  exists
    (fun (s1 : unit * unit * value (circuit_state c3) * unit
             * value (circuit_state (chreset (ndelays (circuit_state c2 * circuit_state c3) n) _))
             * unit)
       (s2 : unit * unit * value (circuit_state (chreset (ndelays (circuit_state c2) n) _))
             * value (circuit_state c3)) =>
       let '(_,_,x1,_,y1,_) := s1 in
       let '(_,_,y2,x2) := s2 in
       x1 = x2
       /\ Forall_ndelays (t1:=_*_) (fun x1 x2 => fst x1 = x2)
                        (from_chreset_state y1) (from_chreset_state y2)).
  cbn [reset_state fst snd Par].
  split.
  { cbn. rewrite !chreset_reset, !from_to_chreset_state.
    ssplit; try reflexivity; [ ].
    apply Forall_ndelays_to_ndelays_state. reflexivity. }
  { cbn [circuit_state LoopInit reset_state value mealy Par].
    intros; destruct_products; logical_simplify. subst.
    cbn [step LoopInit mealy fst snd Par].
    cbv [Combinators.swap]. simpl_ident.
    repeat destruct_pair_let; cbn [fst snd].
    rewrite !step_chreset; cbn [fst snd].
    rewrite !from_to_chreset_state.
    lazymatch goal with
    | H : @Forall_ndelays ?t1 ?t2 ?n ?R ?x1 ?x2 |- _ =>
      let y1 := lazymatch goal with
                | |- context [step (ndelays _ _) x1 ?y1] => y1 end in
      let y2 := lazymatch goal with
                | |- context [step (ndelays _ _) x2 ?y2] => y2 end in
      pose proof (Forall_ndelays_step
                    t1 t2 R x1 x2 y1 y2 H ltac:(reflexivity)) as Hstep
    end.
    cbn [fst snd] in *. destruct Hstep as [Hstep1 Hstep2].
    rewrite Hstep2. ssplit; auto. }
Qed.

(* The structure of this proof is almost identical to retimed_cancel_r, could be
   more automated *)
Lemma retimed_cancel_l {i t o} (c1 c2 : Circuit t o) (c3 : Circuit i t) n :
  is_combinational c3 = true ->
  retimed n c1 c2 ->
  retimed n (c3 >==> c1) (c3 >==> c2).
Proof.
  cbv [retimed]. intros ? [r Heq]; logical_simplify.
  exists r. rewrite Heq. clear Heq.
  cbv [Par]; rewrite !First_Second_comm, !Compose_assoc.
  rewrite !LoopInit_First_r.
  autorewrite with circuitsimpl.
  apply Proper_Compose; [ | reflexivity ].
  rewrite mealy_compose_comb_l by auto.
  repeat match goal with
         | |- context [?a >==> ?b >==> ?c] =>
           lazymatch a with context [First c3] =>
                            rewrite <-(Compose_assoc a b c) end
         end.
  rewrite <-LoopInit_Compose_l.
  apply Proper_Compose; [ reflexivity | ].
  autorewrite with circuitsimpl.
  erewrite (LoopInit_change_state (s1:=circuit_state c3 * circuit_state c2))
    with (f:=snd); [ reflexivity | ].
  cbn [circuit_state reset_state].
  autorewrite with circuitsimpl.
  exists (fun (s1 : unit * unit * unit
             * value (circuit_state (chreset (ndelays (circuit_state c3 * circuit_state c2) n) _))
             * unit)
       (s2 : unit * unit * value (circuit_state (chreset (ndelays (circuit_state c2) n) _))) =>
       let '(_,_,x1,_) := s1 in
       let '(_,_,x2) := s2 in
       Forall_ndelays (t1:=_*_) (fun v1 v2 => snd v1 = v2)
                      (from_chreset_state x1) (from_chreset_state x2)).
  cbn [reset_state circuit_state fst snd Par].
  split.
  { cbn. rewrite !chreset_reset, !from_to_chreset_state.
    ssplit; try reflexivity; [ ].
    apply Forall_ndelays_to_ndelays_state. reflexivity. }
  { cbn [circuit_state LoopInit reset_state value mealy Par].
    intros; destruct_products; logical_simplify. subst.
    cbn [step LoopInit mealy fst snd Par].
    cbv [Combinators.swap]. simpl_ident.
    repeat destruct_pair_let; cbn [fst snd].
    rewrite !step_chreset; cbn [fst snd].
    rewrite !from_to_chreset_state.
    lazymatch goal with
    | H : @Forall_ndelays ?t1 ?t2 ?n ?R ?x1 ?x2 |- _ =>
      let y1 := lazymatch goal with
                | |- context [step (ndelays _ _) x1 ?y1] => y1 end in
      let y2 := lazymatch goal with
                | |- context [step (ndelays _ _) x2 ?y2] => y2 end in
      pose proof (Forall_ndelays_step
                    t1 t2 R x1 x2 y1 y2 H ltac:(reflexivity)) as Hstep
    end.
    cbn [fst snd] in *. destruct Hstep as [Hstep1 Hstep2].
    rewrite Hstep2. ssplit; auto. }
Qed.

Global Instance Reflexive_retimed {i o} : Reflexive (@retimed i o 0) | 10.
Proof. repeat intro. apply retimed_cequiv; reflexivity. Qed.

Lemma Par_LoopInit {i1 o1 s1 i2 o2 s2} (c1 : Circuit (i1 * s1) (o1 * s1))
      (c2 : Circuit (i2 * s2) (o2 * s2)) r1 r2 :
  cequiv (Par (LoopInit r1 c1) (LoopInit r2 c2))
         (LoopInit
            (s:=s1*s2) (r1,r2)
            (Comb (i:=_*_*(_*_)) (o:=_*_*(_*_))
                  (fun '(x1,x2,(s1,s2)) => (x1,s1,(x2,s2)))
                  >==> Par c1 c2
                  >==> (Comb (i:=_*_*(_*_)) (o:=_*_*(_*_))
                             (fun '(x1,s1,(x2,s2)) => (x1,x2,(s1,s2)))))).
Proof.
  exists (fun (x1 : unit * (value (circuit_state c1) * value s1)
             * (unit * (value (circuit_state c2) * value s2)))
       (x2 : unit * (unit * (value (circuit_state c1) * value (circuit_state c2))
                     * unit * (value s1 * value s2))) =>
       let '(_,(a1,b1),(_,(c1,d1))) := x1 in
       let '(_,(_,(a2,c2),_,(b2,d2))) := x2 in
       a1 = a2 /\ b1 = b2 /\ c1 = c2 /\ d1 = d2).
  cbn [reset_state circuit_state value Par LoopInit fst snd].
  ssplit; [ reflexivity .. | ].
  intros; destruct_products; logical_simplify. subst.
  cbn [step LoopInit Par fst snd]. simpl_ident.
  repeat destruct_pair_let. cbn [fst snd].
  ssplit; reflexivity.
Qed.

Lemma mealy_Par {i1 i2 o1 o2} (c1 : Circuit i1 o1) (c2 : Circuit i2 o2) :
  cequiv (mealy (Par c1 c2))
         (Comb (i:=_*_*(_*_)) (o:=_*_*(_*_))
                  (fun '(x1,x2,(s1,s2)) => (x1,s1,(x2,s2)))
                  >==> Par (mealy c1) (mealy c2)
                  >==> (Comb (i:=_*_*(_*_)) (o:=_*_*(_*_))
                             (fun '(x1,s1,(x2,s2)) => (x1,x2,(s1,s2))))).
Proof.
  exists (fun _ _ => True). ssplit; [ tauto | ].
  cbn [value circuit_state Par mealy].
  intros; destruct_products; logical_simplify. subst.
  cbn [step LoopInit Par fst snd mealy].
  cbv [Combinators.swap]. simpl_ident.
  repeat destruct_pair_let. cbn [fst snd].
  ssplit; reflexivity.
Qed.

Lemma split_ndelays_chreset_combine_ndelays {t1 t2} n x y :
  cequiv (chreset (ndelays (t1 * t2) n) (combine_ndelays x y))
         (Par (chreset (ndelays t1 n) x)
              (chreset (ndelays t2 n) y)).
Proof.
  revert x y; induction n;
    cbn [value circuit_state ndelays chreset Id Delay];
    intros; autorewrite with circuitsimpl; [ reflexivity | ].
  destruct_products. cbn [combine_ndelays fst snd].
  rewrite Par_Compose. rewrite IHn.
  rewrite split_delay_init. reflexivity.
Qed.

Lemma to_ndelays_state_combine_ndelays {t1 t2} x n :
  to_ndelays_state (t:=t1*t2) (n:=n) x
  = combine_ndelays (to_ndelays_state (fst x))
                    (to_ndelays_state (snd x)).
Proof.
  revert x; induction n; [ reflexivity | ].
  intros. cbn [to_ndelays_state combine_ndelays fst snd].
  rewrite <-IHn, <-surjective_pairing.
  reflexivity.
Qed.

(* Helper for retimed_par *)
Lemma Par_Par_rearrange1 {i1 i2 i3 i4 o1 o2 o3 o4}
      (c1 : Circuit i1 o1) (c2 : Circuit i2 o2)
      (c3 : Circuit i3 o3) (c4 : Circuit i4 o4) :
  cequiv ((Comb (i:=(_*_*(_*_))) (o:=_*_*(_*_))
                (fun '(x1,x3,(x2,x4)) => (x1,x2,(x3,x4))))
            >==> Par (Par c1 c2) (Par c3 c4))
         ((Par (Par c1 c3) (Par c2 c4))
            >==> (Comb (i:=(_*_*(_*_))) (o:=_*_*(_*_))
                       (fun '(x1,x2,(x3,x4)) => (x1,x3,(x2,x4))))).
Proof.
  exists (fun (lhs : unit * (value (circuit_state c1) * value (circuit_state c2)
                      * (value (circuit_state c3) * value (circuit_state c4))))
       (rhs : value (circuit_state c1) * value (circuit_state c3)
              * (value (circuit_state c2) * value (circuit_state c4)) * unit) =>
       let '(_,(l1,l2,(l3,l4))) := lhs in
       let '(r1,r3,(r2,r4),_) := rhs in
       l1 = r1 /\ l2 = r2 /\ l3 = r3 /\ l4 = r4).
  cbn [reset_state circuit_state value Par fst snd].
  ssplit; [ reflexivity  ..| ].
  intros; destruct_products; logical_simplify. subst.
  cbn [step Par fst snd]. simpl_ident.
  ssplit; reflexivity.
Qed.

Lemma retimed_par {i1 i2 o1 o2}
      (c1 c2 : Circuit i1 o1) (c3 c4 : Circuit i2 o2) n :
  retimed n c1 c2 -> retimed n c3 c4 -> retimed n (Par c1 c3) (Par c2 c4).
Proof.
  cbv [retimed]. cbn [circuit_state Par value]. intros.
  logical_simplify.
  let r1 := lazymatch goal with
              r : value (circuit_state (ndelays o1 _)) |- _ => r end in
  let r2 := lazymatch goal with
              r : value (circuit_state (ndelays o2 _)) |- _ => r end in
  exists (combine_ndelays r1 r2).
  repeat match goal with H : cequiv _ _ |- _ => rewrite H; clear H end.
  rewrite Par_LoopInit.
  eapply Proper_LoopInit; [ reflexivity | ].
  rewrite Par_Compose. rewrite mealy_Par.
  autorewrite with circuitsimpl.
  rewrite to_ndelays_state_combine_ndelays.
  rewrite !split_ndelays_chreset_combine_ndelays.
  rewrite <-(Compose_assoc _ (Comb _) (Par (Par _ _) (Par _ _))).
  rewrite Par_Par_rearrange1.
  autorewrite with circuitsimpl.
  reflexivity.
Qed.

Lemma retimed_delay_init {t} (r : value t) : retimed 1 (DelayInit r) Id.
Proof.
  rewrite <-(Compose_Id_l (DelayInit _)).
  eapply retimed_delay_init_r; reflexivity.
Qed.

Lemma retimed_ndelays {t} n : retimed n (ndelays t n) Id.
Proof.
  induction n; [ reflexivity | ]. cbn [ndelays].
  apply retimed_delay_r; auto.
Qed.

Lemma retimed_first {i o t} (c1 c2 : Circuit i o) n :
  retimed n c1 c2 -> retimed n (Par c1 (ndelays t n)) (First c2).
Proof.
  intros. rewrite <-Par_Id_l.
  apply retimed_par; [ assumption | ].
  apply retimed_ndelays.
Qed.

Lemma retimed_second {i o t} (c1 c2 : Circuit i o) n :
  retimed n c1 c2 -> retimed n (Par (ndelays t n) c1) (Second c2).
Proof.
  intros. rewrite <-Par_Id_r.
  apply retimed_par; [ | assumption ].
  apply retimed_ndelays.
Qed.

Lemma mealy_LoopInit {i o s} (c : Circuit (i * s) (o * s)) r :
  cequiv (mealy (LoopInit r c))
         (Comb (i:=_*(_*(_*_))) (o:=(_*_)*_)
               (fun '(x,(_,(cs,ls))) => ((x,ls),cs))
               >==> mealy c
               >==> (Comb (i:=(_*_)*_) (o:=_*(tzero*(_*_)))
                          (fun '((x,ls),cs) => (x,(tt,(cs,ls)))))).
Admitted.

Lemma combine_ndelays_map_fst_snd
      {t1 t2 n} (r : value (circuit_state (ndelays (t1 * t2) n))) :
  combine_ndelays (map_ndelays (t1:=_*_) fst r)
                  (map_ndelays (t1:=_*_) snd r) = r.
Proof.
  revert r; induction n;
    cbn [value circuit_state reset_state ndelays Id map_ndelays combine_ndelays];
    intros; destruct_products; logical_simplify; [ reflexivity | ].
  cbn [fst snd]. rewrite IHn, <-surjective_pairing; reflexivity.
Qed.

(* Helper lemma for retimed_LoopInit *)
Lemma cequiv_compose_second_ndelays_r_impl
      {i o1 o2} (c1 c2 : Circuit i (o1 * o2)) n x y :
  cequiv (c1 >==> Second (chreset (ndelays o2 n) x))
         (c2 >==> Second (chreset (ndelays o2 n) y)) ->
  x = y.
Proof.
  (* intuition: the first outputs are guaranteed to be x and y respectively, and
     cequiv guarantees same result from simulate, therefore x = y *)
Admitted.

(* TODO: this is a bit of a hack to check the logic; instead of hardwiring the
LHS to have delays at the end, we should instead be able to do this proof by
simply declaring that, for all inputs, the first n state outputs are equal to r,
e.g.
  (forall input,
      map_ndelays (t1:=_*_) (n:=n) snd
                  (ndelays_value_from_sim c1 (reset_state c1) input)
      = to_ndelays_state r) *)
Lemma retimed_LoopInit {i o s} (c1 c2 : Circuit (i * s) (o * s)) n r :
  retimed n (c1 >==> Second (chreset (ndelays s n) (to_ndelays_state r))) c2 ->
  retimed n (LoopInit r (c1 >==> Second (chreset (ndelays s n)
                                                 (to_ndelays_state r))))
          (LoopInit r c2).
Proof.
  intros [v Hv]. rewrite Hv.

  (* manipulate Hv to prove that the second element of v is r repeated *)
  cbv [Par] in Hv. rewrite First_Second_comm, Compose_assoc in Hv.
  rewrite LoopInit_First_r in Hv.
  rewrite <-(combine_ndelays_map_fst_snd v) in Hv.
  rewrite split_ndelays_chreset_combine_ndelays in Hv.
  cbv [Par] in Hv. autorewrite with circuitsimpl in Hv.
  apply cequiv_compose_second_ndelays_r_impl in Hv.
  (* done; we'll use the hypothesis later *)

  rewrite LoopInit_LoopInit.
  autorewrite with circuitsimpl.
  cbv [retimed]. cbn [circuit_state reset_state LoopInit value].
  exists (map_ndelays (t1:=o*s) fst ltac:(eassumption)).
  rewrite mealy_LoopInit.
  rewrite <-(combine_ndelays_map_fst_snd v).
  rewrite !to_ndelays_state_combine_ndelays.
  rewrite !split_ndelays_chreset_combine_ndelays.
  rewrite !combine_ndelays_map_fst_snd.
  erewrite (LoopInit_change_state
              (s1:=tzero*(_*_)) (s2:=_*_))
    with (f:=fun x => (snd (snd x), fst (snd x)));
    [ reflexivity | ].
  fold @value. cbn [fst snd].
  autorewrite with pull_comb circuitsimpl.
  repeat match goal with
         | |- context [?a >==> ?b >==> ?c] =>
           lazymatch a with context [mealy c2] =>
                            rewrite <-(Compose_assoc a b c) end
         end.
  apply Proper_Compose;
    [ erewrite Comb_ext; [ reflexivity | ];
      cbn [value]; intros; destruct_products; reflexivity | ].

  exists (fun (s1 : unit * (value (circuit_state (chreset (ndelays o n) _))
                     * (value (circuit_state (chreset (ndelays tzero n) _))
                        * (value (circuit_state (chreset (ndelays (circuit_state c2) n) _))
                           *  value (circuit_state (chreset (ndelays s n) _))))
                     * unit))
       (s2 : value (circuit_state (chreset (ndelays o n) _))
             * value (circuit_state (chreset (ndelays s n) _))
             * value (circuit_state (chreset (ndelays (circuit_state c2) n) _))
             * unit) =>
       let '(_,(x1,(_,(y1,z1)),_)) := s1 in
       let '(x2,z2,y2,_) := s2 in
       from_chreset_state x1 = from_chreset_state x2
       /\ from_chreset_state y1 = from_chreset_state y2
       /\ from_chreset_state z1 = from_chreset_state z2).
  cbn [reset_state circuit_state value Par fst snd].
  rewrite !chreset_reset, !from_to_chreset_state.
  rewrite Hv. ssplit; [ reflexivity .. | ].
  intros; destruct_products; logical_simplify.
  cbn [step Par fst snd].
  rewrite !step_chreset. cbn [fst snd].
  rewrite !from_to_chreset_state.
  repeat match goal with H : from_chreset_state _ = from_chreset_state _ |- _ =>
                         rewrite H end.
  ssplit; reflexivity.
Qed.

Lemma ndelays_reset {t n} :
  reset_state (ndelays t n) = to_ndelays_state defaultValue.
Proof.
  induction n; [ reflexivity | ]. cbn [ndelays Id Delay reset_state].
  rewrite IHn. reflexivity.
Qed.

Lemma retimed_Loop {i o s} (c1 c2 : Circuit (i * s) (o * s)) n :
  retimed n (c1 >==> Second (ndelays s n)) c2 ->
  retimed n (Loop (c1 >==> Second (ndelays s n))) (Loop c2).
Proof.
  rewrite <-chreset_noop with (c:=ndelays s n).
  rewrite ndelays_reset. intros.
  apply retimed_LoopInit; auto.
Qed.

Local Ltac rewrite_is_combinational :=
  repeat match goal with
         | H : is_combinational _ = true |- _ => rewrite H end.

Require Import Coq.derive.Derive.
Require Import Cava.Lib.Combinators.
Require Import Cava.Lib.CombinatorsProperties.

Derive pipelined_nand
       SuchThat (retimed
                   2 pipelined_nand
                   (Comb (i:=Bit*Bit) (o:=Bit) and2
                         >==> Comb (o:=Bit) inv))
       As pipelined_nand_correct.
Proof.
  (* insert a delay at the end *)
  apply retimed_delay_r; [ reflexivity | ].
  (* add the inv to the pipelined circuit *)
  apply retimed_cancel_r; [ reflexivity | ].
  (* insert another delay *)
  apply retimed_delay_r; [ reflexivity | ].
  (* done! *)
  reflexivity.
Qed.
Print pipelined_nand.
Check pipelined_nand_correct.


Section WithSubroutines.
  Context {state key : type}
          (sbytes : Circuit state state)
          (shrows : Circuit state state)
          (mxcols : Circuit state state)
          (add_rk : Circuit (state * key) state).

  Definition cipher_middle_round : Circuit (state * key) state :=
    First (sbytes >==> shrows >==> mxcols) >==> add_rk.

  Definition cipher : Circuit key state :=
    Loop (Comb (i:=_*_) (o:=_*_) swap
               >==> cipher_middle_round
               >==> Comb (o:=_*_) fork2).
End WithSubroutines.

Derive retimed_cipher_middle_round
       SuchThat
       (forall {state key} n
          (sbytes retimed_sbytes shrows mxcols : Circuit state state)
          (add_rk : Circuit (state * key) state),
           retimed n retimed_sbytes sbytes ->
           is_combinational shrows = true ->
           is_combinational mxcols = true ->
           is_combinational add_rk = true ->
           retimed
             n
             (retimed_cipher_middle_round
                state key n retimed_sbytes shrows mxcols add_rk)
             (cipher_middle_round sbytes shrows mxcols add_rk))
       As retimed_cipher_middle_round_correct.
Proof.
  intros. cbv [cipher_middle_round].
  autorewrite with circuitsimpl.
  apply retimed_cancel_r; [ assumption | ].
  apply retimed_cancel_r; [ assumption | ].
  apply retimed_cancel_r; [ assumption | ].
  apply retimed_first.
  eassumption.
Qed.
Print retimed_cipher_middle_round.
Check retimed_cipher_middle_round_correct.


Derive retimed_cipher
       SuchThat
       (forall {state key} n
          (sbytes retimed_sbytes shrows mxcols : Circuit state state)
          (add_rk : Circuit (state * key) state),
           retimed n retimed_sbytes sbytes ->
           is_combinational sbytes = true ->
           is_combinational shrows = true ->
           is_combinational mxcols = true ->
           is_combinational add_rk = true ->
           retimed
             n
             (retimed_cipher
                state key n retimed_sbytes shrows mxcols add_rk)
             (cipher sbytes shrows mxcols add_rk))
       As retimed_cipher_correct.
Proof.
  intros. cbv [cipher].
  autorewrite with circuitsimpl.
  (* lift loop onto retimed circuit *)
  apply retimed_Loop.
  (* The below is currently broken because of the hacky delays in
  retimed_LoopInit *)
  (*
  (* cancel out combinational components *)
  apply retimed_cancel_r; [ reflexivity | ].
  apply retimed_cancel_l; [ reflexivity | ].
  (*  use the retimed middle round lemma *)
  apply (retimed_cipher_middle_round_correct state); [ | assumption .. ].
  (* done! *)
  eassumption.
  *)
Abort.
