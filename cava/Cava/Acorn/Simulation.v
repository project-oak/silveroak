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

Require Import Coq.Lists.List.
Require Import coqutil.Tactics.Tactics.
Import ListNotations.

Require Import Cava.Util.List.
Require Import Cava.Core.Signal.
Require Import Cava.Util.Tactics.
Require Import Cava.Core.CavaClass.
Require Import Cava.Core.Circuit.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.Identity.

Existing Instance CombinationalSemantics.

(* Run a circuit for many timesteps, starting at the reset value *)
Definition simulate {i o} (c : Circuit i o) (input : list i) : list o :=
  match input with
  | [] => []
  | i :: input =>
    let '(o,st) := step c (reset_state c) i in
    let '(acc, _) := fold_left_accumulate
                       (fun o_st => step c (snd o_st))
                       input (o,st) in
    map fst acc
  end.

Lemma simulate_compose {A B C} (c1 : Circuit A B) (c2 : Circuit B C) (input : list A) :
  simulate (Compose c1 c2) input = simulate c2 (simulate c1 input).
Proof.
  clear.
  cbv [simulate]. destruct input as [|i0 input]; [ reflexivity | ].
  repeat destruct_pair_let.
  destruct input as [|i1 input]; [ cbn; repeat destruct_pair_let; reflexivity | ].
  rewrite !fold_left_accumulate_cons_full.
  cbn [fst snd map step reset_state circuit_state].
  repeat destruct_pair_let. cbn [fst snd].
  rewrite <-!surjective_pairing.
  rewrite fold_left_accumulate_map.
  rewrite fold_left_accumulate_fold_left_accumulate.
  cbn [map]. apply f_equal.
  factor_out_loops.
  eapply fold_left_accumulate_double_invariant
    with (I:=fun (x : B * circuit_state c1 * (C * circuit_state c2))
               (y : C * (circuit_state c1 * circuit_state c2)) =>
               y = (fst (snd x), (snd (fst x), snd (snd x)))).
  { reflexivity. }
  { intros. repeat destruct_pair_let.
    subst. cbn [fst snd]. reflexivity. }
  { intros. subst; destruct_products. cbn [fst snd] in *.
    match goal with H : Forall2 _ _ _ |- _ =>
                    apply Forall2_eq_map_l in H end.
    subst. rewrite !map_map. apply map_ext; intros.
    reflexivity. }
Qed.
Hint Rewrite @simulate_compose using solve [eauto] : push_simulate.

Lemma simulate_comb {A B} (c : A -> ident B) (input : list A) :
  simulate (Comb c) input = map c input.
Proof.
  clear.
  cbv [simulate]. destruct input as [|i0 input]; [ reflexivity | ].
  repeat destruct_pair_let.
  cbn [fst snd map step reset_state circuit_state].
  rewrite fold_left_accumulate_to_map.
  cbn [map fst]. rewrite map_map. cbn [fst].
  reflexivity.
Qed.
Hint Rewrite @simulate_comb using solve [eauto] : push_simulate.

Lemma simulate_first {A B C} (f : Circuit A C) (input : list (A * B)) :
  simulate (First f) input = combine (simulate f (map fst input))
                                      (map snd input).
Proof.
  clear.
  cbv [simulate]. destruct input as [|i0 input]; [ reflexivity | ].
  repeat destruct_pair_let; simpl_ident.
  cbn [fst snd map step reset_state circuit_state].
  simpl_ident. repeat destruct_pair_let; simpl_ident.
  rewrite fold_left_accumulate_map.
  rewrite !fold_left_accumulate_to_seq with (default:=i0).
  factor_out_loops.
  eapply fold_left_accumulate_double_invariant_seq
    with (I:=fun i x y => y = (fst x, snd (nth i (i0::input) i0), snd x)).
  { reflexivity. }
  { intros; subst. destruct_products. cbn [fst snd].
    repeat destruct_pair_let; simpl_ident.
    reflexivity. }
  { intros *. intros ? Hnth; intros.
    change (snd i0 :: map snd input) with (map snd (i0::input)).
    subst. cbn [fst snd].
    eapply list_eq_elementwise; [ length_hammer | ].
    intros j [c b]; intros.
    specialize (Hnth j).
    autorewrite with natsimpl push_length in *.
    autorewrite with push_nth. destruct_products.
    let x := constr:(ltac:(eassumption):circuit_state f) in
    erewrite map_nth_inbounds with (d2:=(c,b,x)) by length_hammer;
      erewrite map_nth_inbounds with (d2:=(c,x)) by length_hammer.
    erewrite Hnth by length_hammer. cbn [fst snd].
    erewrite !map_nth_inbounds by length_hammer.
    reflexivity. }
Qed.
Hint Rewrite @simulate_first using solve [eauto] : push_simulate.

Lemma simulate_second {A B C} (f : Circuit B C) (input : list (A * B)) :
  simulate (Second f) input = combine (map fst input)
                                       (simulate f (map snd input)).
Proof.
  clear.
  cbv [simulate]. destruct input as [|i0 input]; [ reflexivity | ].
  repeat destruct_pair_let; simpl_ident.
  cbn [fst snd map step reset_state circuit_state].
  simpl_ident. repeat destruct_pair_let; simpl_ident.
  rewrite fold_left_accumulate_map.
  rewrite !fold_left_accumulate_to_seq with (default:=i0).
  factor_out_loops.
  eapply fold_left_accumulate_double_invariant_seq
    with (I:=fun i x y => y = (fst (nth i (i0::input) i0), fst x, snd x)).
  { reflexivity. }
  { intros; subst. destruct_products. cbn [fst snd].
    repeat destruct_pair_let; simpl_ident.
    reflexivity. }
  { intros *. intros ? Hnth; intros.
    change (fst i0 :: map fst input) with (map fst (i0::input)).
    subst. cbn [fst snd].
    eapply list_eq_elementwise; [ length_hammer | ].
    intros j [a0 c]; intros.
    specialize (Hnth j).
    autorewrite with natsimpl push_length in *.
    autorewrite with push_nth. destruct_products.
    let x := constr:(ltac:(eassumption):circuit_state f) in
    erewrite map_nth_inbounds with (d2:=(a0,c,x)) by length_hammer;
      erewrite map_nth_inbounds with (d2:=(c,x)) by length_hammer.
    erewrite Hnth by length_hammer. cbn [fst snd].
    erewrite !map_nth_inbounds by length_hammer.
    reflexivity. }
Qed.
Hint Rewrite @simulate_second using solve [eauto] : push_simulate.

Lemma simulate_length {i o} (c : Circuit i o) input :
  length (simulate c input) = length input.
Proof.
  cbv [simulate].
  destruct input; repeat destruct_pair_let; length_hammer.
Qed.
Hint Rewrite @simulate_length using solve [eauto] : push_length.

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
