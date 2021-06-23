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

(* Run a circuit for many timesteps, starting at the reset value *)
Definition simulate {i o} (c : Circuit i o) (input : list (value i)) : list (value o) :=
  fold_left_accumulate (step c) input (reset_state c).

Local Ltac simsimpl :=
  repeat first [ progress cbv [simulate]
               | progress cbn [reset_state circuit_state step fst snd]
               | destruct_pair_let
               | progress simpl_ident ].

Lemma simulate_compose {A B C} (c1 : Circuit A B) (c2 : Circuit B C) (input : list (value A)) :
  simulate (Compose c1 c2) input = simulate c2 (simulate c1 input).
Proof.
  simsimpl.
  rewrite fold_left_accumulate_fold_left_accumulate.
  apply fold_left_accumulate_ext; intros.
  simsimpl. reflexivity.
Qed.
Hint Rewrite @simulate_compose using solve [eauto] : push_simulate.

Lemma simulate_comb {A B} (c : value A -> ident (value B)) (input : list (value A)) :
  simulate (Comb c) input = map c input.
Proof. apply fold_left_accumulate_to_map. Qed.
Hint Rewrite @simulate_comb using solve [eauto] : push_simulate.

Lemma simulate_first {A B C} (f : Circuit A C) (input : list (value (A * B))) :
  simulate (First f) input = combine (simulate f (map fst input))
                                      (map snd input).
Proof.
  simsimpl. rewrite !fold_left_accumulate_map.
  destruct input as [|i0 ?]; [ reflexivity | ].
  rewrite !fold_left_accumulate_to_seq with (default:=i0).
  factor_out_loops.
  eapply fold_left_accumulate_double_invariant_seq
    with (I:= fun i st1 st2 acc1 acc2 =>
                st1 = st2 /\
                length acc2 = i /\
                length acc1 = i /\
                acc2 = combine acc1 (map snd (firstn i (i0 :: input)))).
  { ssplit; reflexivity. }
  { intros; logical_simplify.
    subst acc2; subst.
    autorewrite with push_length natsimpl in *.
    repeat destruct_pair_let; cbn [fst snd].
    ssplit; try reflexivity; try lia; [ ].
    rewrite firstn_succ_snoc with (d:=i0) by length_hammer.
    autorewrite with pull_snoc. rewrite combine_append by length_hammer.
    reflexivity. }
  { intros; logical_simplify; subst.
    autorewrite with push_firstn natsimpl.
    reflexivity. }
Qed.
Hint Rewrite @simulate_first using solve [eauto] : push_simulate.

Lemma simulate_second {A B C} (f : Circuit B C) (input : list (value (A * B))) :
  simulate (Second f) input = combine (map fst input)
                                       (simulate f (map snd input)).
Proof.
  simsimpl. rewrite !fold_left_accumulate_map.
  destruct input as [|i0 ?]; [ reflexivity | ].
  rewrite !fold_left_accumulate_to_seq with (default:=i0).
  factor_out_loops.
  eapply fold_left_accumulate_double_invariant_seq
    with (I:= fun i st1 st2 acc1 acc2 =>
                st1 = st2 /\
                length acc2 = i /\
                length acc1 = i /\
                acc2 = combine (map fst (firstn i (i0 :: input))) acc1).
  { ssplit; reflexivity. }
  { intros; logical_simplify.
    subst acc2; subst.
    autorewrite with push_length natsimpl in *.
    repeat destruct_pair_let; cbn [fst snd].
    ssplit; try reflexivity; try lia; [ ].
    rewrite firstn_succ_snoc with (d:=i0) by length_hammer.
    autorewrite with pull_snoc. rewrite combine_append by length_hammer.
    reflexivity. }
  { intros; logical_simplify; subst.
    autorewrite with push_firstn natsimpl.
    reflexivity. }
Qed.
Hint Rewrite @simulate_second using solve [eauto] : push_simulate.

Lemma simulate_DelayInitCE {t} (init : value t) input :
  simulate (DelayInitCE init) input
  = firstn (length input)
           (init :: (fold_left_accumulate
                      (fun st i_en =>
                         if (snd i_en : bool)
                         then (fst i_en, fst i_en)
                         else (st, st))
                      input init)).
Proof.
  simsimpl. generalize init.
  induction input; intros; [ reflexivity | ].
  autorewrite with push_length push_firstn push_fold_acc.
  cbn [value] in *. destruct_products; cbn [fst snd]. erewrite IHinput.
  simsimpl. destruct_one_match; reflexivity.
Qed.
Hint Rewrite @simulate_DelayInitCE using solve [eauto] : push_simulate.

Lemma simulate_DelayCE {t} (input : list (value t * bool)) :
  simulate DelayCE input = firstn (length input)
                                  (defaultValue
                                     :: (fold_left_accumulate
                                          (fun st i_en =>
                                             if (snd i_en : bool)
                                             then (fst i_en, fst i_en)
                                             else (st, st))
                                          input defaultValue)).
Proof. apply simulate_DelayInitCE. Qed.
Hint Rewrite @simulate_DelayCE using solve [eauto] : push_simulate.

Lemma simulate_DelayInit {t} init (input : list (value t)) :
  simulate (DelayInit init) input = firstn (length input) (init :: input).
Proof.
  cbv [DelayInit]. simpl_ident. autorewrite with push_simulate push_length.
  erewrite fold_left_accumulate_to_seq with (default:=(defaultValue,false)).
  eapply fold_left_accumulate_invariant_seq
    with (I:=fun i (st : value t) acc =>
               acc = firstn i input
               /\ st = nth i (init :: input) defaultValue).
  {  ssplit; reflexivity. }
  { cbv zeta; intro i; intros. subst.
    destruct_products; cbn [fst snd] in *.
    logical_simplify; subst. cbn [fst snd].
    autorewrite with push_length in *.
    autorewrite with push_firstn push_nth pull_snoc natsimpl.
    erewrite !map_nth_inbounds with (d2:=defaultValue) by length_hammer.
    cbn [value] in *.  erewrite firstn_succ_snoc by lia. cbn [fst snd].
    ssplit; reflexivity. }
  { intros. logical_simplify; subst. cbn [fst snd].
    autorewrite with push_length push_firstn.
    reflexivity. }
Qed.
Hint Rewrite @simulate_DelayInit using solve [eauto] : push_simulate.

Lemma simulate_Delay {t} (input : list (value t)) :
  simulate Delay input = firstn (length input) (defaultValue :: input).
Proof. apply simulate_DelayInit. Qed.
Hint Rewrite @simulate_Delay using solve [eauto] : push_simulate.

Lemma simulate_length {i o} (c : Circuit i o) input :
  length (simulate c input) = length input.
Proof.
  simsimpl. generalize (reset_state c).
  induction input; intros; [ reflexivity | ].
  simsimpl. autorewrite with push_length.
  reflexivity.
Qed.
Hint Rewrite @simulate_length using solve [eauto] : push_length.

Lemma simulate_LoopInitCE {i o s}
      resetval (body : Circuit (i * s) (o * s))
      (input : list (value i * bool)) :
  simulate (LoopInitCE resetval body) input =
  fold_left_accumulate
    (fun '(cs, st) '(i, en) =>
       let '(cs', (o, st')) := step body cs (i, st) in
       let new_state := if (en : bool) then st' else st in
       (cs', new_state, o))
    input (reset_state body, resetval).
Proof.
  eapply fold_left_accumulate_ext.
  cbn [circuit_state value]; intros.
  destruct_products. repeat destruct_pair_let.
  reflexivity.
Qed.
Hint Rewrite @simulate_LoopInitCE using solve [eauto] : push_simulate.

Lemma simulate_LoopCE {i o s}
      (body : Circuit (i * s) (o * s))
      (input : list (value i * bool)) :
  simulate (LoopCE body) input =
  fold_left_accumulate
    (fun '(cs, st) '(i, en) =>
       let '(cs', (o, st')) := step body cs (i, st) in
       let new_state := if (en : bool) then st' else st in
       (cs', new_state, o))
    input (reset_state body, defaultValue).
Proof. apply simulate_LoopInitCE. Qed.
Hint Rewrite @simulate_LoopCE using solve [eauto] : push_simulate.

Lemma simulate_LoopInit {i o s}
      resetval (body : Circuit (i * s) (o * s))
      (input : list (value i)) :
  simulate (LoopInit resetval body) input =
  fold_left_accumulate
    (fun '(cs, st) i =>
       let '(cs', (o, st')) := step body cs (i, st) in
       (cs', st', o))
    input (reset_state body, resetval).
Proof.
  cbv [LoopInit]. simpl_ident. autorewrite with push_simulate.
  rewrite fold_left_accumulate_map.
  apply fold_left_accumulate_ext; intros.
  repeat destruct_pair_let. reflexivity.
Qed.
Hint Rewrite @simulate_LoopInit using solve [eauto] : push_simulate.

Lemma simulate_Loop {i o s}
      (body : Circuit (i * s) (o * s))
      (input : list (value i)) :
  simulate (Loop body) input =
  fold_left_accumulate
    (fun '(cs, st) i =>
       let '(cs', (o, st')) := step body cs (i, st) in
       (cs', st', o))
    input (reset_state body, defaultValue).
Proof. apply simulate_LoopInit. Qed.
Hint Rewrite @simulate_Loop using solve [eauto] : push_simulate.
