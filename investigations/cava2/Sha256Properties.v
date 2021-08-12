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
Lemma step_vec_as_tuple_cons {t n} (xs : list (denote_type t)) :
  step (vec_as_tuple (t:=t) (n:=S n)) tt (xs, tt)
  = (tt, (hd default xs, snd (step (vec_as_tuple (t:=t) (n:=n)) tt (tl xs, tt)))).
Proof. reflexivity. Qed.
Hint Rewrite @step_vec_as_tuple_cons using solve [eauto] : stepsimpl.
Lemma step_vec_as_tuple_one {t} (xs : list (denote_type t)):
  step (vec_as_tuple (t:=t) (n:=0)) tt (xs, tt) = (tt, hd default xs).
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

(* TODO: move *)
Lemma resize_length {A} (d : A) n ls : length (List.resize d n ls) = n.
Proof. cbv [List.resize]. length_hammer. Qed.
Hint Rewrite @resize_length using solve [eauto] : push_length.

(* TODO: move *)
Lemma firstn_map_nth {A} (d : A) n ls :
  n <= length ls -> firstn n ls = List.map (fun i : nat => nth i ls d) (seq 0 n).
Proof.
  revert ls; induction n; [ reflexivity | ].
  intros. erewrite firstn_succ_snoc by lia. rewrite IHn by lia.
  autorewrite with pull_snoc. reflexivity.
Qed.

(* TODO: move *)
Lemma resize_map_nth {A} (d : A) n ls :
  List.resize d n ls = List.map (fun i => nth i ls d) (seq 0 n).
Proof.
  intros; subst. cbv [List.resize].
  destr (n <=? length ls);
    autorewrite with natsimpl listsimpl push_firstn;
    [ solve [auto using firstn_map_nth] | ].
  replace n with (length ls + (n - length ls)) by lia.
  rewrite seq_app, map_app, <-firstn_map_nth by lia.
  autorewrite with natsimpl push_firstn. apply f_equal.
  erewrite map_ext_in; [ rewrite map_constant; f_equal; length_hammer | ].
  intros *. rewrite in_seq. intros.
  rewrite nth_overflow by lia; reflexivity.
Qed.

Lemma hd_to_nth {A} (d : A) ls : hd d ls = nth 0 ls d.
Proof. destruct ls; reflexivity. Qed.
Hint Rewrite @hd_to_nth @nth_tl using solve [eauto] : hd_tl_to_nth.

Lemma step_sha256_compress
      (H : denote_type sha_digest)
      (k w : denote_type sha_word) (t i : nat) (msg : list byte) :
  k = nth t SHA256.K 0%N ->
  w = nth t (SHA256.W msg i) 0%N ->
  step sha256_compress tt (H,(k,(w,tt)))
  = (tt, SHA256.sha256_compress msg i (List.resize 0%N 8 H) t).
Proof.
  intros. rewrite resize_map_nth. cbn [List.map seq].
  subst. cbv [sha256_compress]. stepsimpl.
  autorewrite with hd_tl_to_nth.
  reflexivity.
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
  repeat match goal with H : _ = nth ?n _ _ |- _ =>
                         rewrite <-H end.
  cbv [SHA256.add_mod SHA256.w]. N.push_pull_mod.
  cbv [SHA256.sigma1 SHA256.sigma0 SHA256.SHR].
  cbn [N.of_nat Pos.of_succ_nat Pos.succ].
  repeat (f_equal; try lia).
Qed.
Hint Rewrite @step_sha256_message_schedule_update using solve [eauto] : stepsimpl.

(* TODO: move *)
Lemma resize_noop {A} (d : A) n ls :
  n = length ls -> List.resize d n ls = ls.
Proof.
  intros; subst. cbv [List.resize].
  autorewrite with natsimpl listsimpl push_firstn.
  reflexivity.
Qed.

Lemma step_sha256_round_constants (round : denote_type sha_round) :
  step sha256_round_constants tt (round, tt)
  = (tt, nth (N.to_nat round) SHA256.K 0%N).
Proof. reflexivity. Qed.
Hint Rewrite @step_sha256_round_constants using solve [eauto] : stepsimpl.

Definition sha256_inner_spec
           (input : denote_type [Bit; sha_block; sha_digest; Bit])
           (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
           msg (i : nat)
  : denote_type (sha_digest ** sha_block ** Bit ** sha_round)
    * denote_type (sha_digest ** Bit) :=
  let '(block_valid, (block, (initial_digest, clear))) := input in
  let '(current_digest, (message_schedule, (done, round))) := state in
  let inc_round := (done =? 0)%N in
  let start := negb (block_valid =? 0)%N in
  let t := N.to_nat round in
  let next_message_schedule :=
      List.resize 0%N 16 (firstn 16 (skipn (t + 1 - 16) (SHA256.W msg i))) in
  let next_digest := SHA256.sha256_compress msg i current_digest t in
  let next_done := if ((round =? 64)%N || negb (done =? 0)%N)%bool then 1%N else 0%N in
  let next_round := if inc_round then (round + 1)%N else round in
  let next_state := (next_digest, (next_message_schedule, (next_done, next_round))) in
  let out := (map2 N.add initial_digest next_digest, next_done) in
  (next_state, out).

Definition state_of {s i o} (c : @Circuit denote_type s i o) : type := s.
Compute state_of sha256_inner.

(* TODO: move *)
Module List.
  Definition slice {A} (d : A) ls start len : list A :=
    List.resize d len (skipn start ls).
End List.

Lemma nth_skipn {A} (d : A) n i ls :
  nth i (skipn n ls) d = nth (n + i) ls d.
Proof.
  revert i ls; induction n; [ reflexivity | ].
  intros; destruct ls; [ destruct i; reflexivity | ].
  cbn [Nat.add]. autorewrite with push_skipn push_nth.
  rewrite IHn. reflexivity.
Qed.
Hint Rewrite @nth_skipn using solve [eauto] : push_nth.

(* TODO: move *)
Lemma slice_map_nth {A} (d : A) ls start len :
  List.slice d ls start len = List.map (fun i => nth (start + i) ls d) (seq 0 len).
Proof.
  intros; subst. cbv [List.slice].
  rewrite resize_map_nth. apply map_ext; intros.
  autorewrite with push_nth; reflexivity.
Qed.

(* TODO: move *)
Lemma slice_length {A} (d : A) ls start len :
  length (List.slice d ls start len) = len.
Proof. rewrite slice_map_nth. length_hammer. Qed.
Hint Rewrite @slice_length using solve [eauto] : push_length.

(* TODO: move *)
Lemma tl_slice {A} (d : A) ls start len :
  tl (List.slice d ls start (S len)) = List.slice d ls (S start) len.
Proof.
  rewrite !slice_map_nth. cbn [seq List.map tl].
  rewrite <-seq_shift, map_map. apply map_ext; intros.
  f_equal; lia.
Qed.

(* TODO: move *)
Lemma hd_slice {A} (d : A) ls start len :
  hd d (List.slice d ls start (S len)) = nth start ls d.
Proof.
  rewrite !slice_map_nth. cbn [seq List.map hd]. f_equal; lia.
Qed.

Ltac is_projection_from_step e :=
  lazymatch e with
  | fst ?e' => is_projection_from_step e'
  | snd ?e' => is_projection_from_step e'
  | step _ _ _ => idtac
  | _ => fail "term is not a projection from step"
  end.

(* works like destruct_pair_let, but only simplifies expressions with step *)
Ltac destruct_step_pair_let :=
  repeat match goal with
         | |- context [match ?p with
                      | pair _ _ => _ end] =>
           is_projection_from_step p;
           rewrite (surjective_pairing p)
         end.

Print SHA256.sha256_step.
Lemma step_sha256_inner
      (input : denote_type [Bit; sha_block; sha_digest; Bit])
      (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
      msg i :
  (* message schedule = 16 elts of W starting at index round-16 (0 if round <= 16) *)
  fst (snd state) = List.slice 0%N (SHA256.W msg i)
                               (N.to_nat (snd (snd (snd state))) - 16) 16 ->
  step sha256_inner state input = sha256_inner_spec input state msg i.
Proof.
  Set Printing Depth 10000.
  destruct input as (block_valid, (block, (initial_digest, (clear, [])))).
  destruct state as (current_digest, (message_schedule, (done, round))).
  cbn [fst snd]. intros; subst.
  cbv [sha256_inner K]. stepsimpl.
  destruct_step_pair_let. cbn [fst snd].
  rewrite !resize_noop by length_hammer.
  rewrite !tl_slice. rewrite !hd_slice.
  erewrite step_sha256_compress with (t:=N.to_nat round).
  2:{ reflexivity. }
  2:{
  rewrite slice_map_nth. cbn [List.map seq hd tl app].
  rewrite !resize_noop by length_hammer. cbn [tl].
  stepsimpl. destruct_step_pair_let.
  cbn [tl].
  destruct_pair_let; cbn [fst snd].
  destruct_pair_let; cbn [fst snd].
  destruct_pair_let; cbn [fst snd].
  destruct_pair_let; cbn [fst snd].
  destruct_pair_let; cbn [fst snd].
  destruct_pair_let; cbn [fst snd].
  destruct_pair_let; cbn [fst snd].
  destr (15 <=? round)%N.
  { cbn [N.eqb].
    rewrite (surjective_pairing (step sha256_message_schedule_update _ _)).
  erewrite step_sha256_message_schedule_update with (t:=N.to_nat round).
  2:{ f_equal; lia. }
  2:{ f_equal; try lia. }
  2:{ f_equal; lia. }
    rewrite firstn_
  { erewrite step_sha256_compress.
  rewrite step_sha256_round_constants.
  intros. subst; destruct_lists_by_length.
  cbv [sha256_compress]. stepsimpl. reflexivity.
  intro Hschedule. rewrite resize_map_nth in Hschedule.
  cbn [seq List.map] in Hschedule. subst.
  cbv [sha256_inner K]. stepsimpl.
  2:{
    Search nth firstn.
    rewrite firstn_
  { erewrite step_sha256_compress.
  rewrite step_sha256_round_constants.
  intros. subst; destruct_lists_by_length.
  cbv [sha256_compress]. stepsimpl. reflexivity.
Qed.
Hint Rewrite @step_sha256_compress using solve [eauto] : stepsimpl.
