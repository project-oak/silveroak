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
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Import ListNotations.

Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.Identity.

Existing Instance CombinationalSemantics.

Fixpoint simulate_with_state {i o} (c : Circuit i o) (st : circuit_state c) (input : list i)
  : list o * list (circuit_state c) :=
  match input with
  | [] => ([], [])
  | i :: input =>
    let o_st := step c st i in
    let out_states := simulate_with_state c (snd o_st) input in
    (fst o_st :: fst out_states, snd o_st :: snd out_states)
  end.

(*
Fixpoint simulate_init {i o} (c : Circuit i o) (st : circuit_state c) (input : list i) : list o :=
  match input with
  | [] => []
  | i :: input =>
    let o_st := step c st i in
    fst o_st :: simulate_init c (snd o_st) input
  end.*)

(* Run a circuit for many timesteps, starting at the reset value *)
Definition simulate {i o} (c : Circuit i o) (input : list i) : list o :=
  fst (simulate_with_state c (reset_state c) input).

Local Ltac simsimpl :=
  repeat first [ progress cbv [simulate]
               | progress cbn [reset_state circuit_state simulate_with_state step fst snd]
               | destruct_pair_let
               | progress simpl_ident ].

Lemma simulate_compose {A B C} (c1 : Circuit A B) (c2 : Circuit B C) (input : list A) :
  simulate (Compose c1 c2) input = simulate c2 (simulate c1 input).
Proof.
  simsimpl. generalize (reset_state c2), (reset_state c1).
  induction input; intros; [ reflexivity | ].
  simsimpl. rewrite IHinput. reflexivity.
Qed.
Hint Rewrite @simulate_compose using solve [eauto] : push_simulate.

Lemma simulate_comb {A B} (c : A -> ident B) (input : list A) :
  simulate (Comb c) input = map c input.
Proof.
  simsimpl. induction input; [ reflexivity | ].
  simsimpl. rewrite IHinput; reflexivity.
Qed.
Hint Rewrite @simulate_comb using solve [eauto] : push_simulate.

Lemma simulate_first {A B C} (f : Circuit A C) (input : list (A * B)) :
  simulate (First f) input = combine (simulate f (map fst input))
                                      (map snd input).
Proof.
  simsimpl. generalize (reset_state f).
  induction input; intros; [ reflexivity | ].
  simsimpl. rewrite IHinput. reflexivity.
Qed.
Hint Rewrite @simulate_first using solve [eauto] : push_simulate.

Lemma simulate_second {A B C} (f : Circuit B C) (input : list (A * B)) :
  simulate (Second f) input = combine (map fst input)
                                       (simulate f (map snd input)).
Proof.
  simsimpl. generalize (reset_state f).
  induction input; intros; [ reflexivity | ].
  simsimpl. rewrite IHinput. reflexivity.
Qed.
Hint Rewrite @simulate_second using solve [eauto] : push_simulate.

Lemma simulate_DelayInitCE {t} (init : combType t) input :
  simulate (DelayInitCE init) input = firstn (length input)
                                             (init :: fst (fold_left_accumulate
                                                            (fun st i_en =>
                                                               if (snd i_en : bool)
                                                               then fst i_en
                                                               else st)
                                                            input init)).
Proof.
  simsimpl. generalize init at 1. generalize init.
  induction input; intros; [ reflexivity | ].
  simsimpl. rewrite IHinput.
  autorewrite with push_length push_firstn push_fold_acc.
  destruct_products; cbn [fst snd].
  reflexivity.
Qed.
Hint Rewrite @simulate_DelayInitCE using solve [eauto] : push_simulate.

Lemma simulate_DelayCE {t} (input : list (combType t * bool)) :
  simulate DelayCE input = firstn (length input)
                                  (defaultSignal
                                     :: fst (fold_left_accumulate
                                              (fun st i_en =>
                                                 if (snd i_en : bool)
                                                 then fst i_en
                                                 else st)
                                              input defaultSignal)).
Proof. apply simulate_DelayInitCE. Qed.
Hint Rewrite @simulate_DelayCE using solve [eauto] : push_simulate.

Lemma simulate_DelayInit {t} init (input : list (combType t)) :
  simulate (DelayInit init) input = firstn (length input) (init :: input).
Proof.
  cbv [DelayInit]. simpl_ident. autorewrite with push_simulate push_length.
  erewrite fold_left_accumulate_to_seq with (default:=(defaultSignal,false)).
  eapply fold_left_accumulate_invariant_seq
    with (I:=fun i (st : combType t) acc =>
               acc = firstn i input
               /\ st = nth i (init :: input) defaultSignal).
  {  ssplit; reflexivity. }
  { cbv zeta; intro i; intros. subst.
    destruct_products; cbn [fst snd] in *.
    logical_simplify; subst. cbn [fst snd].
    autorewrite with push_length in *.
    autorewrite with push_firstn push_nth pull_snoc natsimpl.
    rewrite !map_nth_inbounds with (d2:=defaultSignal) by length_hammer.
    erewrite firstn_succ_snoc by lia. cbn [fst snd].
    ssplit; reflexivity. }
  { intros. logical_simplify; subst. cbn [fst snd].
    autorewrite with push_length push_firstn.
    reflexivity. }
Qed.
Hint Rewrite @simulate_DelayInit using solve [eauto] : push_simulate.

Lemma simulate_Delay {t} (input : list (combType t)) :
  simulate Delay input = firstn (length input) (defaultSignal :: input).
Proof. apply simulate_DelayInit. Qed.
Hint Rewrite @simulate_Delay using solve [eauto] : push_simulate.

Lemma simulate_length {i o} (c : Circuit i o) input :
  length (simulate c input) = length input.
Proof.
  simsimpl. generalize (reset_state c).
  induction input; intros; [ reflexivity | ].
  simsimpl. autorewrite with push_length.
  rewrite IHinput; reflexivity.
Qed.
Hint Rewrite @simulate_length using solve [eauto] : push_length.

(* simulate_with_state really SHOULD be fold_left_acc, but we need o for it... any way around this? *)
Lemma simulate_with_state_snoc i o (c : Circuit i o) st input i0 :
  simulate_with_state c s (input ++ [i0]) =
Check simulate_with_state (LoopInitCE _ _).
Lemma simulate_LoopInitICE_invariant_helper
      {i s o} resetval (body : Circuit (i * combType s) (o * combType s))
      (I : nat -> combType s -> circuit_state body ->
           list o -> list (circuit_state body * combType s) -> Prop)
      (P : list o * list (circuit_state body * combType s) -> Prop)
      (start_state : circuit_state body * combType s)
      (input : list (i * bool)) :
  (* invariant holds at start *)
  I 0 (snd start_state) (fst start_state) [] [] ->
  (* invariant holds through loop *)
  (forall t out_acc state_acc st bodyst d,
      I t st bodyst out_acc state_acc ->
      0 <= t < length input ->
      let input_en := nth t input d in
      let out_st'_bodyst' := step body bodyst (fst input_en, st) in
      let out := fst (fst out_st'_bodyst') in
      let st' := snd (fst out_st'_bodyst') in
      let bodyst' := snd out_st'_bodyst' in
      let new_state := if snd input_en then st' else st in
      I (S t) new_state bodyst'
        (out_acc ++ [out])
        (state_acc ++ [(bodyst', new_state)])) ->
  (* invariant implies postcondition *)
  (forall out_acc state_acc st bodyst,
      I (length input) st bodyst out_acc state_acc ->
      P (out_acc, state_acc)) ->
  P (simulate_with_state (LoopInitCE resetval body) start_state input).
Proof.
  intros Istart Ipreserved IimpliesP.
  let sim_result := lazymatch goal with
                      |- P ?x => x end in
  rewrite (surjective_pairing sim_result);
    pose (final_state := last (snd sim_result) start_state).
  eapply IimpliesP with (st:=snd final_state) (bodyst:=fst final_state).
  induction input using rev_ind; [ eassumption | ].
  autorewrite with push_length. rewrite Nat.add_1_r.
  apply Ipreserved.
  simsimpl.
Qed.

Lemma simulate_LoopInitICE_invariant
      {i s o} resetval (body : Circuit (i * combType s) (o * combType s))
      (I : nat -> combType s -> circuit_state body -> list o -> Prop ) (P : list o -> Prop)
      (input : list (i * bool)) :
  (* invariant holds at start *)
  I 0 resetval (reset_state body) [] ->
  (* invariant holds through loop *)
  (forall t acc st bodyst d,
      I t st bodyst acc ->
      0 <= t < length input ->
      let input_en := nth t input d in
      let out_st'_bodyst' := step body bodyst (fst input_en, st) in
      let out := fst (fst out_st'_bodyst') in
      let st' := snd (fst out_st'_bodyst') in
      let bodyst' := snd out_st'_bodyst' in
      let new_state := if snd input_en then st' else st in
      I (S t) new_state bodyst' (acc ++ [out])) ->
  (* invariant implies postcondition *)
  (forall acc st bodyst, I (length input) st bodyst acc -> P acc) ->
  P (simulate (LoopInitCE resetval body) input).
Proof.
  intros Istart Ipreserved IimpliesP.
  simsimpl.
  (* get the list of states *)
  lazymatch goal with
  | |- context [simulate-
  pose (snd 
  pose (fold_left (fun st i_en =>
                     let x := step body (fst st) (fst i_en, snd st) in
                     (snd x, if (snd i_en : bool) then snd (fst x) else snd st))
                  input (reset_state body, resetval)) as final_state.
  apply IimpliesP with (st:=snd final_state) (bodyst:=fst final_state).
  subst final_state.
  generalize resetval at 3.
  generalize dependent (reset_state body).
  generalize dependent resetval.
  induction input; intros; [ eassumption | ].
  simsimpl. autorewrite with push_length.
  destruct_products. cbn [fst snd fold_left].
  eapply Ipreserved.
  rewrite IHinput.
  generalize resetval at 1.
  generalize (reset_state body), resetval.
  induction input; intros; [ solve [eauto] | ].
  simsimpl.
  1:cbn.
  1:eauto.
  destruct input; [ solve [eauto] | ].
  repeat destruct_pair_let.
  cbn [circuit_state reset_state step fst snd].
  apply fold_left_accumulate_invariant_seq
    with (I0:=fun t '(out,(bodyst,st)) acc =>
                I (S t) st bodyst (map fst acc));
    intros *; repeat destruct_pair_let; cbn [fst snd].
  { specialize (Ipreserved 0 []). cbn [nth app length] in Ipreserved.
    cbn [map fst snd]. eapply Ipreserved; eauto; [ ]. Lia.lia. }
  { intros. specialize (Ipreserved (S t)).
    autorewrite with pull_snoc.
    eapply Ipreserved; eauto; [ ].
    cbn [combType] in *; length_hammer. }
  { eapply IimpliesP. }



  
  intros ? Ipreserved IimpliesP. cbv [simulate].
  destruct input; [ solve [eauto] | ].
  repeat destruct_pair_let.
  cbn [circuit_state reset_state step fst snd].
  apply fold_left_accumulate_invariant_seq
    with (I0:=fun t '(out,(bodyst,st)) acc =>
                I (S t) st bodyst (map fst acc));
    intros *; repeat destruct_pair_let; cbn [fst snd].
  { specialize (Ipreserved 0 []). cbn [nth app length] in Ipreserved.
    cbn [map fst snd]. eapply Ipreserved; eauto; [ ]. Lia.lia. }
  { intros. specialize (Ipreserved (S t)).
    autorewrite with pull_snoc.
    eapply Ipreserved; eauto; [ ].
    cbn [combType] in *; length_hammer. }
  { eapply IimpliesP. }
Qed.

Lemma simulate_LoopCE_invariant
      {i s o} (body : Circuit (i * combType s) (o * combType s))
      (I : nat -> combType s -> circuit_state body -> list o -> Prop ) (P : list o -> Prop)
      (input : list (i * bool)) :
  (* invariant holds at start *)
  I 0 (defaultCombValue _) (reset_state body) [] ->
  (* invariant holds through loop *)
  (forall t acc st bodyst d,
      I t st bodyst acc ->
      0 <= t < length input ->
      let input_en := nth t input d in
      let out_st'_bodyst' := step body bodyst (fst input_en, st) in
      let out := fst (fst out_st'_bodyst') in
      let st' := snd (fst out_st'_bodyst') in
      let bodyst' := snd out_st'_bodyst' in
      let new_state := if snd input_en then st' else st in
      I (S t) new_state bodyst' (acc ++ [out])) ->
  (* invariant implies postcondition *)
  (forall acc st bodyst, I (length input) st bodyst acc -> P acc) ->
  P (simulate (LoopCE body) input).
Proof. apply simulate_LoopInitICE_invariant. Qed.

Lemma simulate_LoopInit_invariant
      {i s o} resetval (body : Circuit (i * combType s) (o * combType s))
      (I : nat -> combType s -> circuit_state body -> list o -> Prop ) (P : list o -> Prop)
      (input : list i) :
  (* invariant holds at start *)
  I 0 resetval (reset_state body) [] ->
  (* invariant holds through loop *)
  (forall t acc st bodyst d,
      I t st bodyst acc ->
      0 <= t < length input ->
      let out_st'_bodyst' := step body bodyst (nth t input d, st) in
      let out := fst (fst out_st'_bodyst') in
      let st' := snd (fst out_st'_bodyst') in
      let bodyst' := snd out_st'_bodyst' in
      I (S t) st' bodyst' (acc ++ [out])) ->
  (* invariant implies postcondition *)
  (forall acc st bodyst, I (length input) st bodyst acc -> P acc) ->
  P (simulate (LoopInit resetval body) input).
Proof.
  intros? Ipres IimpliesP; cbv [LoopInit].
  autorewrite with push_simulate. simpl_ident.
  eapply simulate_LoopInitICE_invariant with (I0:=I).
  { eassumption. }
  { cbv zeta in *. intros *. destruct_products.
    autorewrite with push_length. intros.
    let d := lazymatch goal with x : i |- _ => x end in
    rewrite map_nth_inbounds with (d2:=d) by length_hammer.
    cbn [fst]. apply Ipres; auto. }
  { intros *; autorewrite with push_length.
    apply IimpliesP. }
Qed.

Lemma simulate_Loop_invariant
      {i s o} (body : Circuit (i * combType s) (o * combType s))
      (I : nat -> combType s -> circuit_state body -> list o -> Prop ) (P : list o -> Prop)
      (input : list i) :
  (* invariant holds at start *)
  I 0 (defaultCombValue _) (reset_state body) [] ->
  (* invariant holds through loop *)
  (forall t acc st bodyst d,
      I t st bodyst acc ->
      0 <= t < length input ->
      let out_st'_bodyst' := step body bodyst (nth t input d, st) in
      let out := fst (fst out_st'_bodyst') in
      let st' := snd (fst out_st'_bodyst') in
      let bodyst' := snd out_st'_bodyst' in
      I (S t) st' bodyst' (acc ++ [out])) ->
  (* invariant implies postcondition *)
  (forall acc st bodyst, I (length input) st bodyst acc -> P acc) ->
  P (simulate (Loop body) input).
Proof. apply simulate_LoopInit_invariant. Qed.
