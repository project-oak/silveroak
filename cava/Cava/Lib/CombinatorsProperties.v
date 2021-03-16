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
Require Import Coq.Vectors.Vector.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Core.Core.
Require Import Cava.Lib.Combinators.
Require Import Cava.Lib.VecProperties.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.Identity.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.Vector.
Import ListNotations VectorNotations.

Lemma fork2Correct {A} (i : combType A) :
 fork2 i = (i, i).
Proof. reflexivity. Qed.
Hint Rewrite @fork2Correct using solve [eauto] : simpl_ident.

(* Full description of the behavior of col_generic *)
Lemma col_generic_correct {A B C} (circuit : A * B -> C * A)
      (a : A) (b : list B) (c : C) :
  let loop := fold_left_accumulate
                (fun ca b => circuit (snd ca, b))
                b (c, a) in
  col_generic circuit a b = (tl (map fst (fst loop)), snd (snd loop)).
Proof.
  cbv zeta; revert a c; induction b; intros; [ reflexivity | ].
  cbn [col_generic]. simpl_ident. repeat destruct_pair_let.
  rewrite fold_left_accumulate_cons_full.
  erewrite IHb by auto. cbn [fst snd map tl].
  apply f_equal2; [ | rewrite <-surjective_pairing; reflexivity ].
  destruct b; autorewrite with push_fold_acc; reflexivity.
Qed.

(* Stepwise description of the behavior of col_generic *)
Lemma col_generic_step {A B C} (circuit : A * B -> combType C * A)
      (a : A) b0 (b : list B) :
  let ca := circuit (a, b0) in
  let rem := col_generic circuit (snd ca) b in
  col_generic circuit a (b0 :: b) = ((fst ca :: fst rem)%list, snd rem).
Proof.
  cbn [col_generic]. simpl_ident.
  repeat destruct_pair_let. reflexivity.
Qed.

(* Full description of the behavior of col *)
Lemma col_correct {A B C} (circuit : A * B -> combType C * A)
      (a : A) {n} (b : Vector.t B n) :
  let loop := fold_left_accumulate
                (fun ca b => circuit (snd ca, b))
                (to_list b) (defaultSignal , a) in
  col circuit a b = (of_list_sized defaultSignal n (tl (map fst (fst loop))),
                     snd (snd loop)).
Proof.
  cbv [col]. simpl_ident. repeat destruct_pair_let.
  erewrite col_generic_correct; reflexivity.
Qed.

(* Stepwise description of the behavior of col *)
Lemma col_step {A B C} (circuit : A * B -> combType C * A)
      (a : A) {n} (b : Vector.t B (S n)) :
  let ca := circuit (a, Vector.hd b) in
  let rem := col circuit (snd ca) (Vector.tl b) in
  col circuit a b = (fst ca :: fst rem, snd rem).
Proof.
  cbv [col]. simpl_ident. repeat destruct_pair_let.
  rewrite (Vector.eta b). cbn [fst snd].
  autorewrite with push_to_list push_of_list_sized vsimpl.
  rewrite col_generic_step. cbn [fst snd].
  autorewrite with push_to_list push_of_list_sized vsimpl.
  reflexivity.
Qed.

(* Helper lemma for bounds of right child trees *)
Lemma tree_generic_bounds_helper n u l :
  2 * l < n <= 2 * u ->
  l < n - n / 2 <= u.
Proof.
  intros [Hlower Hupper].
  pose proof (Nat.div_mod n 2 ltac:(lia)) as ndivmod.
  rewrite <-Nat.bit0_mod in ndivmod.
  rewrite ndivmod in Hupper, Hlower.
  destruct (Nat.testbit n 0); cbn [Nat.b2n] in *; lia.
Qed.

Lemma tree_generic_equiv
      {T} (id : T) (op : T -> T -> T)
      (op_id_left : forall a : T, op id a = a)
      (op_id_right : forall a : T, op a id = a)
      (op_assoc :
         forall a b c : T,
           op a (op b c) = op (op a b) c)
      (def : T) (n : nat) :
  forall inputs,
    0 < length inputs <= 2 ^ n ->
    tree_generic op def n inputs = List.fold_left op inputs id.
Proof.
  induction n; intros.
  { (* depth = 0; input must be a singleton list *)
    subst. autorewrite with natsimpl in *.
    change (2 ^ 0) with 1 in *.
    assert (length inputs = 1) by lia.
    destruct_lists_by_length. cbn [tree_generic fold_left].
    rewrite op_id_left. reflexivity. }
  { (* 0 < depth *)
    cbn [tree_generic]. rewrite Nat.pow_succ_r in * by lia.
    destruct_one_match;
      [ | assert (length inputs = 1) by lia;
          destruct_lists_by_length; cbn [fold_left];
          rewrite op_id_left; reflexivity ].
    pose proof (Nat.div_le_upper_bound (length inputs) 2 (2^n) ltac:(lia) ltac:(lia)).
    pose proof (Nat.div_le_upper_bound (length inputs) 2 (length inputs) ltac:(lia) ltac:(lia)).
    rewrite !IHn by (autorewrite with push_length natsimpl; try apply tree_generic_bounds_helper;
                     auto; split; auto using Nat.div_str_pos).
    simpl_ident.
    rewrite <-fold_left_assoc, <-fold_left_app by eauto.
    rewrite firstn_skipn. reflexivity. }
Qed.

Lemma tree_equiv {t} :
  forall (id : combType t) (op : combType t * combType t -> combType t),
    (forall a : combType t, op (id, a) = a) ->
    (forall a : combType t, op (a, id) = a) ->
    (forall a b c : combType t, op (a, op (b, c)) = op (op (a, b), c)) ->
    forall (n : nat) (v : combType (Vec t n)),
      n <> 0 ->
      tree op v = Vector.fold_left (fun a b => op (a,b)) id v.
Proof.
  intros. cbv [tree]. simpl_ident.
  pose proof Nat.log2_log2_up_spec n ltac:(lia).
  erewrite tree_generic_equiv; eauto; simpl_ident;
    autorewrite with push_length push_to_list;
    reflexivity || lia.
Qed.
