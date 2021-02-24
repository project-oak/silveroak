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

Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.IdentityNew.

(* Run a circuit for many timesteps, starting at the reset value *)
Definition multistep {i o} (c : Circuit i o) (input : list i) : list o :=
  match input with
  | [] => []
  | i :: input =>
    let '(o,st) := unIdent (interp c (reset_state c) i) in
    let '(acc, _) := fold_left_accumulate
                       (fun o_st i => unIdent (interp c (snd o_st) i))
                       input (o,st) in
    map fst acc
  end.

Lemma multistep_compose {A B C} (c1 : Circuit A B) (c2 : Circuit B C) (input : list A) :
  multistep (Compose c1 c2) input = multistep c2 (multistep c1 input).
Proof.
  clear.
  cbv [multistep]. destruct input as [|i0 input]; [ reflexivity | ].
  repeat destruct_pair_let; simpl_ident.
  destruct input as [|i1 input]; [ cbn; repeat destruct_pair_let; reflexivity | ].
  rewrite !fold_left_accumulate_cons_full.
  cbn [fst snd map interp reset_state circuit_state].
  repeat first [ destruct_pair_let | progress simpl_ident ].
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
  { intros. repeat first [ destruct_pair_let | progress simpl_ident ].
    subst. cbn [fst snd]. reflexivity. }
  { intros. subst; destruct_products. cbn [fst snd] in *.
    match goal with H : Forall2 _ _ _ |- _ =>
                    apply Forall2_eq_map_l in H end.
    subst. rewrite !map_map. apply map_ext; intros.
    reflexivity. }
Qed.
Hint Rewrite @multistep_compose using solve [eauto] : push_multistep.

Lemma multistep_comb {A B} (c : A -> ident B) (input : list A) :
  multistep (Comb c) input = map (fun a => unIdent (c a)) input.
Proof.
  clear.
  cbv [multistep]. destruct input as [|i0 input]; [ reflexivity | ].
  repeat destruct_pair_let; simpl_ident.
  cbn [fst snd map interp reset_state circuit_state].
  simpl_ident. rewrite fold_left_accumulate_to_map.
  cbn [map fst]. rewrite map_map. cbn [fst].
  reflexivity.
Qed.
Hint Rewrite @multistep_comb using solve [eauto] : push_multistep.

Lemma multistep_first {A B C} (f : Circuit A C) (input : list (A * B)) :
  multistep (First f) input = combine (multistep f (map fst input))
                                      (map snd input).
Proof.
  clear.
  cbv [multistep]. destruct input as [|i0 input]; [ reflexivity | ].
  repeat destruct_pair_let; simpl_ident.
  cbn [fst snd map interp reset_state circuit_state].
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
Hint Rewrite @multistep_first using solve [eauto] : push_multistep.

Lemma multistep_second {A B C} (f : Circuit B C) (input : list (A * B)) :
  multistep (Second f) input = combine (map fst input)
                                       (multistep f (map snd input)).
Proof.
  clear.
  cbv [multistep]. destruct input as [|i0 input]; [ reflexivity | ].
  repeat destruct_pair_let; simpl_ident.
  cbn [fst snd map interp reset_state circuit_state].
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
Hint Rewrite @multistep_second using solve [eauto] : push_multistep.

Lemma multistep_length {i o} (c : Circuit i o) input :
  length (multistep c input) = length input.
Proof.
  cbv [multistep].
  destruct input; repeat destruct_pair_let; length_hammer.
Qed.
Hint Rewrite @multistep_length using solve [eauto] : push_length.

