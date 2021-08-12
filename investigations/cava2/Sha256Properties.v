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
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.Sha256.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.NPushPullMod.
Require HmacSpec.SHA256.
Import ListNotations.

(* TODO: move to a more general file *)
Lemma step_vec_as_tuple_cons {t n} x0 (xs : list (denote_type t)) :
  step (vec_as_tuple (t:=t) (n:=S n)) tt (x0 :: xs, tt)
  = (tt, (x0, snd (step (vec_as_tuple (t:=t) (n:=n)) tt (xs, tt)))).
Proof. reflexivity. Qed.
Hint Rewrite @step_vec_as_tuple_cons using solve [eauto] : stepsimpl.
Lemma step_vec_as_tuple_one {t} (x : denote_type t):
  step (vec_as_tuple (t:=t) (n:=0)) tt ([x], tt) = (tt, x).
Proof. reflexivity. Qed.
Hint Rewrite @step_vec_as_tuple_one using solve [eauto] : stepsimpl.
Ltac stepsimpl :=
  repeat first [ progress
                   cbn [fst snd step denote_type absorb_any
                            split_absorbed_denotation combine_absorbed_denotation
                            unary_semantics binary_semantics ]
               | progress autorewrite with stepsimpl ].

Lemma step_index {t n i} (x : denote_type (Vec t n))
      (idx : denote_type (BitVec i)) :
  step (@index _ t n i) tt (x, (idx, tt))
  = (tt, nth (N.to_nat idx) (List.resize default n x) default).
Proof. reflexivity. Qed.
Hint Rewrite @step_index using solve [eauto] : stepsimpl.

Lemma step_rotr n (x : denote_type sha_word) :
  step (rotr n) tt (x,tt) = (tt, SHA256.ROTR (N.of_nat n) x).
Proof.
  cbv [rotr]. stepsimpl.
  cbv [SHA256.ROTR SHA256.truncating_shiftl SHA256.w].
  repeat (f_equal; try lia).
Qed.
Hint Rewrite @step_rotr using solve [eauto] : stepsimpl.

Lemma step_sha256_compress
      (H : denote_type sha_digest)
      (k w : denote_type sha_word) (t i : nat) (msg : list byte) :
  length H = 8 ->
  k = nth t SHA256.K 0%N ->
  w = nth t (SHA256.W msg i) 0%N ->
  step sha256_compress tt (H,(k,(w,tt)))
  = (tt, SHA256.sha256_compress msg i H t).
Proof.
  intros. subst; destruct_lists_by_length.
  cbv [sha256_compress]. stepsimpl. reflexivity.
Qed.
Hint Rewrite @step_sha256_compress using solve [eauto] : stepsimpl.


(* TODO: move to Spec.SHA256Properties *)
Lemma nth_W msg (i t : nat) :
  (t < 64) ->
  nth t (SHA256.W msg i) 0%N =
  if (t <? 16)%nat
  then SHA256.M msg t i
  else
    let W_tm2 := nth (t - 2) (SHA256.W msg i) 0%N in
    let W_tm7 := nth (t - 7) (SHA256.W msg i) 0%N in
    let W_tm15 := nth (t - 15) (SHA256.W msg i) 0%N in
    let W_tm16 := nth (t - 16) (SHA256.W msg i) 0%N in
    SHA256.add_mod
      (SHA256.add_mod
         (SHA256.add_mod
            (SHA256.sigma1 W_tm2) W_tm7) (SHA256.sigma0 W_tm15))
      W_tm16.
Proof.
  intros.
  (* extract the formula for an element of W and remember it *)
  lazymatch goal with
    | |- nth t ?W ?d = ?rhs =>
      let f := lazymatch (eval pattern t in rhs) with
               | ?f _ => f end in
      let f := lazymatch (eval pattern W in f) with
               | ?f _ => f end in
      set (W_formula:=f);
        change (nth t W d = W_formula W t)
  end.
  (* use an invariant *)
  apply fold_left_invariant_seq
    with (I:= fun n W =>
                length W = n /\
                forall t, t < n -> nth t W 0%N = W_formula W t)
         (P:=fun W => nth t W 0%N = W_formula W t);
    [ intros; ssplit; length_hammer
    | | intros; ssplit; logical_simplify; solve [auto] ].
  intros. autorewrite with natsimpl push_nth in *.
  logical_simplify. ssplit; [ length_hammer | ]. intros.
  lazymatch goal with H : ?t < S ?n |- context [nth ?t] =>
                      destr (t <? n); [ | replace t with n in * by lia ]
  end; subst W_formula; cbn beta; autorewrite with natsimpl push_nth;
    [ solve [auto] | ].
  destruct_one_match; autorewrite with push_nth; reflexivity.
Qed.

Lemma step_sha256_message_schedule_update
      (w0 w1 w9 w14 : denote_type sha_word) (t i : nat) msg :
  w0 = nth (t-16) (SHA256.W msg i) 0%N ->
  w1 = nth (t-15) (SHA256.W msg i) 0%N ->
  w9 = nth (t-7) (SHA256.W msg i) 0%N ->
  w14 = nth (t-2) (SHA256.W msg i) 0%N ->
  (16 <= t < 64) ->
  step sha256_message_schedule_update tt (w0, (w1, (w9, (w14, tt))))
  = (tt, nth t (SHA256.W msg i) 0%N).
Proof.
  intros. cbv [sha256_message_schedule_update]. stepsimpl.
  rewrite nth_W by lia. destruct_one_match; [ lia | ].
  repeat match goal with H : _ = nth _ _ _ |- _ =>
                         rewrite <-H end.
  cbv [SHA256.add_mod SHA256.w]. N.push_pull_mod.
  cbv [SHA256.sigma1 SHA256.sigma0 SHA256.SHR].
  cbn [N.of_nat Pos.of_succ_nat Pos.succ].
  repeat (f_equal; try lia).
Qed.
Hint Rewrite @step_sha256_message_schedule_update using solve [eauto] : stepsimpl.

Lemma step_sha256_round_constants (round : denote_type sha_round) :
  step sha256_round_constants tt (round, tt)
  = (tt, nth (N.to_nat round) SHA256.K 0%N).
Proof. reflexivity. Qed.
Hint Rewrite @step_sha256_round_constants using solve [eauto] : stepsimpl.
