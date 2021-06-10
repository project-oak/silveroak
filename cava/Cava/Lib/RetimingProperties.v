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
Require Import Cava.Semantics.Simulation.
Require Import Cava.Semantics.WeakEquivalence.
Require Import Cava.Lib.CircuitTransforms.
Require Import Cava.Lib.CircuitTransformsProperties.
Require Import Cava.Lib.Retiming.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Import ListNotations Circuit.Notations.

(* starting from scratch with retiming lemmas! Might not even need cequivn now. *)

Fixpoint multi_loop {i o s}
  : Circuit (i * ivalue s) (o * ivalue s) -> ivalue s -> Circuit i o :=
  match s with
  | ione t => fun c resetval => LoopInit resetval c
  | ipair t1 t2 =>
    fun (c : Circuit (i * (ivalue t1 * ivalue t2))
                   (o * (ivalue t1 * ivalue t2)))
      (resetvals : ivalue t1 * ivalue t2) =>
      multi_loop
        (multi_loop
           (Comb (fun '(i,s1,s2) => ret (i,(s1,s2)))
                 >==> c
                 >==> Comb (fun '(o,(s1,s2)) => ret (o,s1,s2)))
           (snd resetvals))
        (fst resetvals)
  end.

Fixpoint loops_reset_state {i o} (c : Circuit i o)
  : ivalue (signal:=combType) (loops_state c) :=
  match c as c in Circuit i o return ivalue (loops_state c) with
  | Comb _ => tt
  | First f => loops_reset_state f
  | Second f => loops_reset_state f
  | Compose f g => (loops_reset_state f, loops_reset_state g)
  | DelayInitCE r => tt
  | LoopInitCE r body => (loops_reset_state body, r)
  end.

(* counts # delays on the critical path *)
Fixpoint cpath_delay {i o} (c : Circuit i o) : nat :=
  match c with
  | Comb _ => 0
  | First f => cpath_delay f
  | Second f => cpath_delay f
  | Compose f g => cpath_delay f + cpath_delay g
  | DelayInitCE r => 1
  | LoopInitCE r body => cpath_delay body
  end.

Inductive is_loop_free : forall {i o}, Circuit i o -> Prop :=
| is_loop_free_comb : forall {i o} (f : i -> cava o), is_loop_free (Comb f)
| is_loop_free_first :
    forall {i t o} f, is_loop_free f -> is_loop_free (@First _ _ i t o f)
| is_loop_free_second :
    forall {i t o} f, is_loop_free f -> is_loop_free (@Second _ _ i t o f)
| is_loop_free_compose :
    forall {i t o} f g, is_loop_free f -> is_loop_free g ->
                   is_loop_free (@Compose _ _ i t o f g)
| is_loop_free_delay : forall {t} r, is_loop_free (@DelayInitCE _ _ t r)
.

Definition extract_loops {i o} (c : Circuit i o) : Circuit i o :=
  multi_loop (loopless c) (loops_reset_state c).

Lemma is_loop_free_loopless {i o} (c : Circuit i o) : is_loop_free (loopless c).
Proof. induction c; cbn [loopless]; repeat constructor; eauto. Qed.

Lemma extract_loops_equiv {i o} (c : Circuit i o) : cequiv (extract_loops c) c.
Proof.
Admitted.

Lemma cequivn_reflexive_loop_free i o (c : Circuit i o) :
  is_loop_free c -> cequivn (cpath_delay c) c c.
Proof.
  induction 1; cbn [cpath_delay].
  { exists eq. cbn [circuit_state]. ssplit; intros.
    all:destruct_lists_by_length; subst.
    all:repeat lazymatch goal with x : unit |- _ => destruct x end.
    all:ssplit; reflexivity. }
  { lazymatch goal with
    | H : cequivn _ _ _ |- _ => destruct H as [R [Hstart HR]]
    end.
    exists R; cbn [circuit_state]; ssplit; intros;
      [ autorewrite with push_repeat_step; apply Hstart; length_hammer | ].
    cbn [step]. repeat (destruct_pair_let; cbn [fst snd]).
    destruct_products; cbn [fst snd].
    specialize (HR _ _ ltac:(eassumption) ltac:(eassumption)).
    logical_simplify. ssplit; congruence. }
  { lazymatch goal with
    | H : cequivn _ _ _ |- _ => destruct H as [R [Hstart HR]]
    end.
    exists R; cbn [circuit_state]; ssplit; intros;
      [ autorewrite with push_repeat_step; apply Hstart; length_hammer | ].
    cbn [step]. repeat (destruct_pair_let; cbn [fst snd]).
    destruct_products; cbn [fst snd].
    specialize (HR _ _ ltac:(eassumption) ltac:(eassumption)).
    logical_simplify. ssplit; congruence. }
  { lazymatch goal with
    | H : cequivn _ _ f |- _ => destruct H as [R1 [Hstart1 HR1]]
    end.
    lazymatch goal with
    | H : cequivn _ _ g |- _ => destruct H as [R2 [Hstart2 HR2]]
    end.
    exists (fun st1 st2 => R1 (fst st1) (fst st2) /\ R2 (snd st1) (snd st2)).
    cbn [circuit_state]; ssplit; intros.
    { ssplit.
      { autorewrite with push_repeat_step. cbn [fst snd].
        eapply state_relation_repeat_step_longer; eauto;
        length_hammer. }
      { erewrite <-(firstn_skipn (cpath_delay f) input).
        rewrite !repeat_step_app.
        autorewrite with push_repeat_step. cbn [fst snd].
        erewrite state_relation_fold_left_accumulate_step
          by (eauto; eapply Hstart1; length_hammer).
        eapply Hstart2. length_hammer. } }
    { cbn [step]. repeat (destruct_pair_let; cbn [fst snd]).
      destruct_products; cbn [fst snd] in *.
      specialize (HR1 _ _ ltac:(eassumption) ltac:(eassumption)).
      lazymatch goal with
      | |- context [step g _ ?i] =>
        specialize (HR2 _ _ i ltac:(eassumption))
      end.
      logical_simplify. ssplit; congruence. } }
  { exists eq. cbn [circuit_state].
    ssplit; intros; [ | subst; ssplit; reflexivity ].
    destruct_lists_by_length; subst.
    autorewrite with push_repeat_step.
    cbn [step]. repeat (destruct_pair_let; cbn [fst snd]).
    (* damn it, doesn't work because delay might be disabled *)
Abort.

Lemma ndelays0_is_id {t} (c : Circuit t t) : is_ndelays 0 c -> c = Id.
Proof. inversion 1; subst; reflexivity. Qed.

Lemma phase_retimed_retimed_iff {i o} m (c1 c2 : Circuit i o) :
  phase_retimed 0 m c1 c2 <-> retimed m c1 c2.
Admitted.

(*
Lemma invert_delays'_par {t1 t2} (c : Circuit (ivalue (ipair t1 t2)) (ivalue (ipair t1 t2))) :
  is_delays' _ c ->
  exists d1 d2, is_delays' t1 d1 /\ is_delays' t2 d2 /\ c = Par d1 d2.
Proof.
  inversion 1. inversion_sigma; subst.
  do 2 eexists; ssplit; eauto.
  rewrite <-Eqdep_dec.eq_rect_eq_dec by apply itype_eq_dec.
  reflexivity.
Qed.

Lemma invert_delays'_delay {t} (c : Circuit (ivalue (ione t)) (ivalue (ione t))) :
  is_delays' _ c -> exists r, c = DelayInit r.
Proof.
  inversion 1. inversion_sigma; subst.
  rewrite <-Eqdep_dec.eq_rect_eq_dec by apply itype_eq_dec.
  eexists; reflexivity.
Qed.

Lemma split_delays {t1 t2} (c : Circuit (t1 * t2) (t1 * t2)) :
  is_delays c ->
  exists (d1 : Circuit t1 t1) (d2 : Circuit t2 t2),
    is_delays d1 /\ is_delays d2 /\ c = Par d1 d2.
Proof.
  inversion 1. inversion_sigma; subst.
  destruct t.
  { eapply invert_delays'_delay in H2.
    logical_simplify; subst.
    Search unit.
    inversion H. inversion_sigma.
    cbn [ivalue] in *. subst.
    rewrite H4 in *.
    do 2 eexists.
    rewrite f_equal_dep.
  eapply split_delays' in H2.
  rewrite H4 in *.
  do 2 eexists.
  rewrite <-Eqdep_dec.eq_rect_eq_dec by apply itype_eq_dec.
Qed.


Lemma split_ndelays {t1 t2} n (c : Circuit (t1 * t2) (t1 * t2)) :
  is_ndelays n c ->
  exists (d1 : Circuit t1 t1) (d2 : Circuit t2 t2),
    is_ndelays n d1 /\ is_ndelays n d2 /\ cequiv c (Par d1 d2).
Proof.
  inversion 1.
  induction 1.
Qed.
*)

Lemma phase_retimed_LoopInit
      {i o s} n m (c1 c2 : Circuit (i * combType s) (o * combType s)) r :
  phase_retimed n m c1 c2 ->
  phase_retimed (S n) m (LoopInit r (Second Delay >==> c1)) (LoopInit r c2).
Proof.
  intros [state_delays [input_delays [proj ?]]].
  logical_simplify.
  exists (Par Delay (Par state_delays Delay)).
  exists (Comb (fun i => ret (i, defaultCombValue s))
          >==> input_delays
          >==> Comb (fun '(i,s) => ret i)).
  cbn [loops_state LoopInit ivalue].
Qed.

(* phase_retimed n m c1 c2 -> is_ndelays m d ->
   phase_retimed n m (Loop (Second d >==> c1)) (Loop c2) *)
Print retimed.
Print phase_retimed.
(* retimed is NOT related to cequivn as stated, because cequivn says everything
   will always stabilize after a certain number of inputs and that's just not
   true within loops. equiv is actually weaker because it says they must be in
   the same start state.

   What about phase_retimed? That one *is* related, because we have the
   guarantee that the circuit is loopless.

   Actually, no it's not, because we could have *disabled* delays inside the
   circuit and that would mean state could linger longer.


   What we really need for loops is not quite cequivn; we need a guarantee that
   after an equal input, N cycles later the circuits will produce an equal output.

 *)

(* forall c, cequivn (ncycles c) c c *)
(* forall c1 c2, cequiv c1 c2 -> ncycles c1 = ncycles c2 /\ cequivn (ncycles c1) c1 c2*)
(* cequiv c1 c2 -> cequivn c1 c3 -> cequivn n c2 c3? *)


(* is_delays c1 -> is_delays c2 -> cequivn 1 c1 c2 *)
(* cequivn n c2 -> is_delays d1 -> is_delays d2 -> cequivn (S n) (c1 >==> d) (c2 >==> d) *)
(* is_ndelays n c1 -> is_ndelays n c2 -> cequivn n c1 c2 *)

(* retimed n c1 c2 -> is_delays d -> retimed (S n) (c1 >==> d) c2 *)
(* retimed 0 c1 c2 <-> cequiv c1 c2 *)
(* cequiv c1 c2 -> retimed n c1 c3 -> retimed n c2 c3 *)
(* cequiv c1 c2 -> retimed n c3 c1 -> retimed n c3 c2 *)
(* is_delays d -> exists d', is_delays d' /\ cequiv (d >==> c) (c >==> d') *)
(* is_delays d1 -> is_delays d2  -> cequivn (c >==> d1) (c >==> d2) *)
(* is_delays d -> is_delays d' -> cequivn 1 (d >==> c) (c >==> d') *)
(* is_ndelays n d -> is_ndelays n d' -> cequivn n (d >==> c) (c >==> d') *)

(* cequiv n c1 c2 -> retimed n c1 c3 -> retimed n c2 c3 *)

(* is_delays d -> retimed n (c >==> d) *)
(* is_delays d -> exists d', is_delays d' /\ cequiv (d >==> c) (c >==> d') *)

(* retimed n c1 c2 <-> phase_retimed n 0 c1 c2 *)
(* phase_retimed n m c1 c2 -> is_ndelays m d ->
   phase_retimed n m (Loop (Second d >==> c1)) (Loop c2) *)


































Lemma retimed_cequiv_iff {i o} n (c1 c2 : Circuit i (ivalue o)) :
  retimed n c1 c2 <-> (exists d, cequivn n d (ndelays n o)
                          /\ cequiv c1 (c2 >==> d)).
Proof.
  (* do we need this lemma? *)
Admitted.

(*
Lemma retimed0_cequiv_iff {i o} (c1 c2 : Circuit i (ivalue o)) :
  retimed 0 c1 c2 -> cequiv c1 c2.
Proof.
  cbv [retimed ndelays]. autorewrite with circuitsimpl.
  intros.
  apply cequivn_cequiv.
  split.
  { intros [resetvals ?]. logical_simplify.
    destruct resetvals; [ | cbn [length] in *; lia ].
    cbn [ndelays fold_left] in *.
    autorewrite with circuitsimpl in *. auto. }
  { intros. exists nil. ssplit; [ reflexivity | ].
    cbn [ndelays fold_left].
    autorewrite with circuitsimpl. auto. }
Qed.

(* rephrasing of the definition of retimed that can be helpful when proving a
   retimed goal *)
Lemma retimed_cequiv {i o} n (c1 c2 : Circuit i (ivalue o)) resetvals :
  cequiv c1 (c2 >==> ndelays o resetvals) ->
  length resetvals = n ->
  retimed n c1 c2.
Proof. cbv [retimed]; intros; eauto. Qed.
 *)

Lemma simulate_delays t input :
  simulate (delays t) input = firstn (length input) (idefault t :: input).
Proof.
  revert input; induction t; intros; cbn [delays ivalue idefault];
    autorewrite with push_simulate; [ reflexivity | ].
  rewrite !IHt1, IHt2. autorewrite with push_length.
  rewrite <-combine_firstn. cbn [combine].
  rewrite combine_map_r, combine_map_l, combine_same.
  rewrite !map_map. cbn [fst snd].
  rewrite List.map_id_ext by (intros; symmetry; apply surjective_pairing).
  reflexivity.
Qed.
Hint Rewrite @simulate_delays using solve [eauto] : push_simulate.

Lemma delays_get_reset t  :
  delays_get (reset_state (delays t)) = idefault t.
Proof.
  induction t; [ reflexivity | ].
  cbn [delays delays_get Par reset_state fst snd].
  rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma delays_get_step t st input :
  delays_get (fst (step (delays t) st input)) = input.
Proof.
  induction t; [ reflexivity | ].
  cbn [delays delays_get Par step fst snd].
  repeat (destruct_pair_let; cbn [fst snd]).
  rewrite IHt1, IHt2, <-surjective_pairing.
  reflexivity.
Qed.

Lemma step_delays t st input :
  snd (step (delays t) st input) = delays_get st.
Proof.
  induction t; [ reflexivity | ].
  cbn [delays delays_get Par step fst snd].
  repeat (destruct_pair_let; cbn [fst snd]).
  rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma is_delays_cequivn t (c1 c2 : Circuit t t) :
  is_delays c1 -> is_delays c2 -> cequivn 1 c1 c2.
Admitted.

Lemma is_ndelays_cequivn t n (c1 c2 : Circuit t t) :
  is_ndelays n c1 -> is_ndelays n c2 -> cequivn n c1 c2.
Admitted.

Lemma fold_left_accumulate_step_DelayInit t (resetval : combType t) input st :
  fold_left_accumulate (step (DelayInit resetval)) input st
  = firstn (length input) (snd st :: input).
Proof.
  revert st. cbv [DelayInit]. simpl_ident. cbn [circuit_state step].
  induction input; intros; [ reflexivity | ].
  autorewrite with push_length push_firstn push_fold_acc.
  destruct_products; cbn [fst snd]. erewrite IHinput.
  reflexivity.
Qed.

Lemma move_DelayInit i o n (c1 c2 : Circuit (combType i) (combType o))
      resetvali resetvalo :
  cequivn n c1 c2 ->
  cequivn (S n) (c1 >==> DelayInit resetvalo) (DelayInit resetvali >==> c2).
Proof.
  intros [R [? HR]].
  exists (fun (st1 : circuit_state c1 * (unit * combType o))
       (st2 : unit * combType i * circuit_state c2) =>
       R (fst st1) (fst (step c2 (snd st2) (snd (fst st2))))
       /\ snd (step c2 (snd st2) (snd (fst st2))) = snd (snd st1)).
  ssplit.
  { cbn [circuit_state]; intro input; intros.
    destruct input using rev_ind; [ cbn [length] in *; lia | ].
    clear IHinput.
    autorewrite with push_repeat_step push_fold_acc; cbn [fst snd].
    rewrite fold_left_accumulate_step_DelayInit.
    autorewrite with push_length. rewrite ?Nat.add_1_r.
    autorewrite with push_firstn natsimpl listsimpl.
    cbn [step DelayInit]. simpl_ident.
    autorewrite with push_repeat_step.
    ssplit.
    { lazymatch goal with
      | |- R (fst (step c1 ?s1 ?x)) (fst (step c2 ?s2 ?x)) =>
        assert (R s1 s2)
      end.
      { Search repeat_step.
        apply state_relation_repeat_step.
      eapply HR.
      rewrite fold_left_accumulate_step_DelayInit.
      autorewrite with push_length. rewrite Nat.add_1_r.
      autorewrite with push_firstn natsimpl listsimpl.
      Search fold_left_accumulate.
      Search repeat_step.
      eapply H.
    cbv [DelayInit]. cbn [step circuit_state]. simpl_ident.
    ssplit.
    { Search repeat_step.
      eapply state_relation_repeat_step.
    rewrite <-surjective_pairing.
Qed.


Lemma move_delays i o (c1 : Circuit i o) c2 c3 :
  is_delays c2 -> is_delays c3 ->
  cequivn 1 (c1 >==> c2) (c3 >==> c1).
Proof.
  revert c3; induction 1.
  { destruct 1.
    { 
Qed.

Lemma is_delays_cequivn_compose t n (c1 c2 c3 : Circuit t t) :
  is_delays n c1 -> is_delays n c2 ->
  cequivn d (c3 >==> c1) (c3 >==> c2) = cequivn (m - n).
Admitted.

Search cequivn.
Lemma is_ndelays_cequivn_compose t n (c1 c2 c3 : Circuit t t) :
  is_ndelays n c1 -> is_ndelays n c2 ->
  cequivn n (c3 >==> c1) (c3 >==> c2) = cequivn (m - n).
Admitted.

Lemma retimed_cequivn i o n (c1 c2 c3 : Circuit i o) :
  retimed n c1 c2 -> retimed n c1 c3 -> cequivn n c2 c3.
Proof.
  cbv [retimed]; intros. logical_simplify.
  rewrite H2 in H1.
  etransitivity.
  { symmetry.
  Search cequivn.
Qed.

Lemma move_delays i o n (c1 c2 : Circuit (ivalue i) (ivalue o)) :
  cequivn n c1 c2 ->
  cequivn (S n) (delays i >==> c1) (c2 >==> delays o).
Proof.
  intros.
  etransitivity.
  (* transitivity, replace delays with some delays that have the reset values for c1 (defaults) *)
  (* OR transitivity, then use cequivn compose-delay lemmas *)
  eapply cequivn_compose with (n0:=1) (m:=n).
  
  intros [R [? ?]].
  exists (fun (st1 : circuit_state (delays i) * circuit_state c1)
       (st2 : circuit_state c2 * circuit_state (delays o)) =>
       exists st1',
         step c1 (snd st1) (delays_get (fst st1)) = (st1', delays_get (snd st2))).
  ssplit.
  { cbn [circuit_state]. intro input; intros.
    destruct input using rev_ind; [ cbn [length] in *; lia | ].
    clear IHinput. autorewrite with push_repeat_step.
    rewrite !fold_left_accumulate_snoc. cbn [fst snd].
    autorewrite with push_repeat_step push_fold_acc.
    destruct_products; cbn [fst snd] in *.
    rewrite !step_delays, !delays_get_step.
    rewrite H0.
    eexists.
    
    repeat (destruct_pair_let; cbn [fst snd]).
    rewrite !delays_get_step, !step_delays.
  { cbn. rewrite !delays_get_reset.
    destruct (step c (reset_state c) resetvalsi); cbn [fst snd] in *.
    logical_simplify; subst. reflexivity. }
  { cbn [circuit_state step]; intros *. intro Hstep.
    destruct_products; cbn [fst snd] in *.
    repeat (destruct_pair_let; cbn [fst snd]).
    logical_simplify. rewrite !delays_get_step, !step_delays.
    rewrite Hstep. cbn [fst snd]. rewrite <-surjective_pairing.
    ssplit; reflexivity. }
Qed.

Lemma move_delays i o (c : Circuit (ivalue i) (ivalue o)) resetvalsi resetvalso :
  (* step c applied to resetvals from resetstate needs to result in reset
     state; otherwise first results don't match *)
  step c (reset_state c) resetvalsi = (reset_state c, resetvalso) ->
  cequiv (delays i resetvalsi >==> c)
         (c >==> delays o resetvalso).
Proof.
  intro Hreset.
  exists (fun (st1 : circuit_state (delays i resetvalsi) * circuit_state c)
       (st2 : circuit_state c * circuit_state (delays o resetvalso)) =>
       step c (snd st1) (delays_get (fst st1)) = (fst st2, delays_get (snd st2))).
  ssplit.
  { cbn. rewrite !delays_get_reset.
    destruct (step c (reset_state c) resetvalsi); cbn [fst snd] in *.
    logical_simplify; subst. reflexivity. }
  { cbn [circuit_state step]; intros *. intro Hstep.
    destruct_products; cbn [fst snd] in *.
    repeat (destruct_pair_let; cbn [fst snd]).
    logical_simplify. rewrite !delays_get_step, !step_delays.
    rewrite Hstep. cbn [fst snd]. rewrite <-surjective_pairing.
    ssplit; reflexivity. }
Qed.

Lemma ndelays_cons t resetvals r0 :
  cequiv (ndelays t (r0 :: resetvals)) (ndelays t resetvals >==> delays t r0).
Proof. reflexivity. Qed.

Lemma ndelays_snoc t resetvals r0 :
  cequiv (ndelays t (resetvals ++ [r0])) (delays t r0 >==> ndelays t resetvals).
Proof.
  revert r0. induction resetvals; intros.
  { cbn [app ndelays]. autorewrite with circuitsimpl. reflexivity. }
  { cbn [app ndelays]. rewrite IHresetvals, Compose_assoc.
    reflexivity. }
Qed.

Lemma simulate_ndelays t resetvals input :
  simulate (ndelays t resetvals) input
  = firstn (length input) (resetvals ++ input).
Proof.
  revert input; induction resetvals; intros.
  { autorewrite with push_simulate listsimpl push_firstn.
    reflexivity. }
  { rewrite ndelays_cons.
    autorewrite with push_simulate push_length.
    rewrite IHresetvals, <-app_comm_cons.
    destruct input; [ reflexivity | ].
    autorewrite with push_length push_firstn natsimpl.
    apply Min.min_case_strong; intros; [ | reflexivity ].
    autorewrite with natsimpl push_firstn listsimpl.
    reflexivity. }
Qed.
Hint Rewrite @simulate_ndelays using solve [eauto] : push_simulate.

Global Instance Proper_retimed i o :
  Proper (eq ==> cequiv ==> cequiv ==> iff) (@retimed i o).
Proof.
  repeat intro. cbv [retimed].
  split; intros; logical_simplify; subst;
    eexists; (ssplit; [ reflexivity | ]).
  all:repeat match goal with H : cequiv _ _ |- _ => rewrite H in * end.
  all:reflexivity.
Qed.

Global Instance Reflexive_retimed0 i o : Reflexive (@retimed i o 0) | 10.
Proof.
  repeat intro; subst.
  exists []; ssplit; [ reflexivity | ].
  cbn [ndelays]. autorewrite with circuitsimpl.
  reflexivity.
Qed.

Lemma retimed_step_r {i o} n (c1 c2 : Circuit i (ivalue o)) resetvals :
  retimed n c1 (c2 >==> delays o resetvals) ->
  retimed (S n) c1 c2.
Proof.
  intros. cbv [retimed] in *. logical_simplify; subst.
  eexists (_++ [_]). autorewrite with push_length.
  rewrite Nat.add_1_r. ssplit; [ reflexivity | ].
  rewrite ndelays_snoc, Compose_assoc. eauto.
Qed.

Lemma retimed_transitivity {i o} n m (c1 c2 c3 : Circuit i (ivalue o)) :
  retimed n c1 c2 ->
  retimed m c2 c3 ->
  retimed (n+m) c1 c3.
Proof.
  revert c1 c2 c3 n; induction m; intros *.
  { rewrite retimed0_cequiv_iff.
    autorewrite with natsimpl.
    intros ? Heq. rewrite <-Heq; eauto. }
  { intros ? [vals [? Heq]]. rewrite Nat.add_succ_r.
    destruct vals using rev_ind; [ cbn [length] in *; lia | ].
    eapply retimed_step_r. eapply IHm; eauto; [ ].
    rewrite ndelays_snoc, !Compose_assoc in *.
Abort.


(*

Can we prove that for every circuit, there exists n, c2 such that retimed n c1 (Comb c2)?

If so, maybe we can prove move_ndelays for Comb only, and use that to prove retimed_step_l...
 *)

Print retimed.
(* need to be equivalent to c2 >==> delays

   (delays >==> c2) will be equivalent to starting c2 at the state that results
   from the reset value of the delays

   (c2 >==> delays) will be just starting c2 as usual and then adding some
   different outputs to the beginning, which is why it's different

   R : circuit_state c1 -> ivalue i -> circuit_state c2 -> Prop

   R (reset_state c1) resetvalsi (reset_state c2)

   preserved_over_step c1 (delays >==> c2) R

   need to prove exists R' : circuit_state c1 -> ivalue o -> circuit_state c2 ->
   Prop such that R' (reset_state c1) resetvalso (reset_state c2) and
   preserved_over_step c1 (c2 >==> delays) R'


   IDEA: Can this be proven the *other* way around? i.e. if retimed means the
   delay is tacked on the front, then can we prove the delay can be tacked on
   the end?

   we can get the values from running the circuit; right now we have to prove
   the inputs exist

   potential problem still: the state of the circuit for input 0 for delays >==>
   c2 would still be the state after getting all the reset values, while the
   state for c2 >==> delays would be the reset state first
 *)
Lemma retimed_step_l {i o} n (c1 c2 : Circuit (ivalue i) (ivalue o)) resetvals :
  retimed n c1 (delays i resetvals >==> c2) ->
  retimed (S n) c1 c2.
Proof.
  intro Hretimed. pose proof Hretimed.
  destruct Hretimed as [? [? [R ?]]].
  logical_simplify; subst.
  eapply retimed_step_r.
  cbn [ndelays]. rewrite Compose_assoc.
  ssplit.
  2:{
    cbn [circuit_state reset_state] in *.
    exists (fun (st1 : circuit_state c1)
         (st2 : circuit_state c2 * circuit_state (ndelays _ _)
                * circuit_state (delays _ _)) =>
         exists (vali : circuit_state (delays i resetvals)),
           R st1 (vali, fst (fst st2), snd (fst st2))).
    ssplit; [ eauto | ]. cbn [circuit_state].
    intros; logical_simplify.
    destruct_products; cbn [fst snd] in *.
    ssplit.
    { cbn.
      repeat destruct_pair_let; cbn [fst snd].


    
  rewrite move_delays in H0.
  ssplit; [ reflexivity | ].
  rewrite ndelays_snoc, Compose_assoc. eauto.
Qed.

Lemma move_delays_retimed {i o} n (c1 c2 : Circuit (ivalue i) (ivalue o))
      resetvalsi resetvalso :
  retimed (S n) c1 (delays i resetvalsi >==> c2) ->
  retimed (S n) c1 (c2 >==> delays o resetvalso).
Proof.
  intros [vals [? Hequiv]]. (* destruct Hequiv as [R [? ?]]]]. *)
  destruct vals as [|v0 vals]; [ cbn [length] in *; lia | ].
  cbn [ndelays circuit_state reset_state] in *.
  
Qed.


Require Import Coq.derive.Derive.

Derive pipelined_nand
       SuchThat (retimed (o:=ione Bit) 2 pipelined_nand
                         (Comb and2 >==> Comb inv))
       As pipelined_nand_correct.
Proof.
  eapply retimed_step; [ reflexivity | ].
  eapply retimed_step; [ reflexivity | ].
  apply retimed0_cequiv_iff.
  rewrite <-move_delays with (i:=ipair (ione Bit) (ione Bit))
    by (cbn; repeat destruct_pair_let; reflexivity).
  rewrite <-Compose_assoc.
  rewrite <-move_delays with (i:=ione Bit)
    by (cbn; repeat destruct_pair_let; reflexivity).
  instantiate (1:=((false,false) : ivalue (signal:=combType) (ipair (ione Bit) (ione Bit)))).
  cbn [fst snd andb delays]. autorewrite with circuitsimpl.
  rewrite !Compose_assoc. subst pipelined_nand.
  reflexivity.
Qed.
Print pipelined_nand.

Lemma ndelays_get_reset t resetvals :
  ndelays_get (reset_state (ndelays t resetvals)) = resetvals.
Proof.
  induction resetvals; [ reflexivity | ].
  cbn [ndelays ndelays_get delays_get reset_state fst snd].
  rewrite delays_get_reset, IHresetvals.
  reflexivity.
Qed.

Lemma step_ndelays t resetvals st input :
  snd (step (ndelays t resetvals) st input) = hd input (ndelays_get st).
Proof.
  induction resetvals; [ reflexivity | ].
  cbn [ndelays ndelays_get step].
  repeat (destruct_pair_let; cbn [fst snd]).
  rewrite IHresetvals, step_delays. reflexivity.
Qed.

Lemma hd_snoc {A} d (l : list A) : hd d (l ++ [d]) = hd d l.
Proof. destruct l; reflexivity. Qed.

Lemma ndelays_get_step t resetvals st input :
  ndelays_get (fst (step (ndelays t resetvals) st input))
  = tl (ndelays_get st ++ [input]).
Proof.
  induction resetvals; [ reflexivity | ].
  cbn [ndelays ndelays_get step fst snd].
  repeat (destruct_pair_let; cbn [fst snd]).
  rewrite delays_get_step, IHresetvals, step_ndelays.
  rewrite <-app_comm_cons. cbn [hd tl].
  etransitivity; [ | symmetry; apply eta_list; length_hammer ].
  rewrite hd_snoc. reflexivity.
Qed.

Lemma move_ndelays i o (c : Circuit (ivalue i) (ivalue o)) resetvalsi resetvalso :
  (*
  (* step c applied to resetvals from resetstate needs to result in reset
     state; otherwise first results don't match *)
  step c (reset_state c) resetvalsi = (reset_state c, resetvalso) ->*)
  cequiv (ndelays i resetvalsi >==> c)
         (c >==> ndelays o resetvalso).
Proof.
  assert (length resetvalsi = length resetvalso) by admit.
  revert c; revert dependent resetvalso;
    induction resetvalsi; destruct resetvalso; intros;
    cbn [length] in *; try lia; [ | ].
  { cbn [ndelays]. autorewrite with circuitsimpl. reflexivity. }
  { cbn [ndelays]. rewrite Compose_assoc.
    erewrite <-(move_delays _ o).
    2:{
      cbn. repeat destruct_pair_let.
      rewrite !step_ndelays.
      rewrite ndel
      f_equal. 1:f_equal.
      
      rewrite <-surjective_pairing.
    rewrite <-(Compose_assoc _ _ _ _ (ndelays _ _)).
    rewrite IHresetvalsi.
    
    Check move_delays.
  intro Hreset.
  exists (fun (st1 : circuit_state (delays i resetvalsi) * circuit_state c)
       (st2 : circuit_state c * circuit_state (delays o resetvalso)) =>
       step c (snd st1) (delays_get (fst st1)) = (fst st2, delays_get (snd st2))).
  ssplit.
  { cbn. rewrite !delays_get_reset.
    destruct (step c (reset_state c) resetvalsi); cbn [fst snd] in *.
    logical_simplify; subst. reflexivity. }
  { cbn [circuit_state step]; intros *. intro Hstep.
    destruct_products; cbn [fst snd] in *.
    repeat (destruct_pair_let; cbn [fst snd]).
    logical_simplify. rewrite !delays_get_step, !step_delays.
    rewrite Hstep. cbn [fst snd]. rewrite <-surjective_pairing.
    ssplit; reflexivity. }
Qed.

Lemma simulate_retimed
      {i o} (n : nat) (c1 c2 : Circuit i (ivalue (signal:=combType) o)) input :
  retimed n c1 c2 ->
  skipn n (simulate c1 input) = firstn (length input - n) (simulate c2 input).
Proof.
  intros [? [? Heq]]. rewrite Heq.
  autorewrite with push_simulate push_length.
  rewrite skipn_firstn_comm. subst.
  autorewrite with push_skipn natsimpl.
  reflexivity.
Qed.

Lemma retimed_compose A B C n m
      (c1 c2 : Circuit A (ivalue B)) (c3 c4 : Circuit (ivalue B) (ivalue C)) :
  retimed n c1 c2 -> retimed m c3 c4 -> retimed (n+m) (c1 >==> c3) (c2 >==> c4).
Proof.
  intros [? [? Heq12]] [? [? Heq34]]. rewrite Heq12, Heq34.
Qed.




















(*
Lemma retimed_sum {i o} (n m: nat) (c1 c2 c3 : Circuit i o) :
  retimed (n+m) c1 c2 -> retimed n c1 c3 -> retimed m c2 c3.
Proof.
  intros [R12 [? H12]]. intros [R13 [? H13]].
  exists (fun i (st2 : circuit_state c2) (st3 : circuit_state c3) =>
       exists st1, R12 i st1 st2
              /\ R13 (Nat.modulo (i*m) n) st1 st3).
  ssplit.
  { exists (reset_state c1). ssplit; eauto.
Qed.
*)

(*
Lemma retimed_delays1_l_iff {i o} (n : nat) (c1 c2 : Circuit (ivalue i) o) :
  retimed 1 c1 c2
  <-> (exists resetvals : ivalue i,
        cequiv c1 (delays i resetvals >==> c2)).
Admitted.
 *)

(*
the second part matches every m cycles
the first part matches every n cycles

assume m=2, n=3

0:reset
2:second part matches
3:first part matches
4:second part matches
6:first part matches
??????
ahhhh, the second part matches only m cycles *after its input matches*



if we are i steps away from matching...

if i <= m,
 the second part is i steps away from matching
else
 second part unclear but does have an R


 *)

Lemma retimed_compose A B C n m (c1 c2 : Circuit A B) (c3 c4 : Circuit B C) :
  retimed n c1 c2 -> retimed m c3 c4 -> retimed (n+m) (c1 >==> c3) (c2 >==> c4).
Proof.
  intros [R12 [? H12]] [R34 [? H34]].
  exists (fun i st1 st2 =>
       R12 (i - m) (fst st1) (fst st2)
       /\ R34 i (snd st1) (snd st2)).
  cbn [reset_state fst snd].
  ssplit;
    [ autorewrite with natsimpl;
      solve [eauto] | | ].
  { 
  cbn [circuit_state]. intros.
  destruct_products; cbn [fst snd] in *.
  logical_simplify. destruct_one_match.
  { autorewrite with natsimpl in *.
    cbn [step]. repeat (destruct_pair_let; cbn [fst snd]).
    specialize (H34 0 _ _ (ltac:(eassumption)) (ltac:(lia))
                    (ltac:(eassumption))).
    cbn iota in H34. destruct H34 as [H34 ?].
    rewrite H34 in *.
  { 
Qed.

Lemma retimed_succ {i o} n (c1 c2 : Circuit (ivalue i) o) :
  retimed (S n) c1 c2 ->
  exists resetvals, retimed n c1 (delays i resetvals >==> c2).
Proof.
Qed.

Lemma retimed_ndelays_l_iff {i o} (n : nat) (c1 c2 : Circuit (ivalue i) o) :
  retimed n c1 c2 <-> (exists resetvals : list (ivalue i),
                        length resetvals = n
                        /\ cequiv c1 (ndelays i resetvals >==> c2)).
Proof.
  split.
  { revert i o c1 c2; induction n; intros *.
    { rewrite retimed_cequiv_iff.
      intros. exists nil. cbn [ndelays fold_left].
      autorewrite with circuitsimpl.
      ssplit; eauto. }
    {
      (* retimed (S n) c1 c2 -> exists c3, retimed n c1 c3 /\ cequiv c3 (delays >==> c2) *)
      
      intros [R [? HR]]. logical_simplify.
    

    (*
      equivalence state relation should say that R 0 holds on the last?
    *)

    evar (r: list (ivalue (signal:=combType) i)).
    exists r. ssplit.
    2:{
      exists (fun (st1 : circuit_state c1)
           (st2 : circuit_state (ndelays i r) * circuit_state c2) =>
           R 0 st1 (snd st2)).
      
Qed.

