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
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.If.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import HmacSpec.SHA256Properties.
Require Import HmacHardware.Sha256.
Require HmacSpec.SHA256.
Import ListNotations.

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
  k = nth t SHA256.K 0%N ->
  w = nth t (SHA256.W msg i) 0%N ->
  step sha256_compress tt (H,(k,(w,tt)))
  = (tt, SHA256.sha256_compress msg i (List.resize 0%N 8 H) t).
Proof.
  intros. rewrite resize_map_nth. cbn [List.map seq].
  subst. cbv [sha256_compress]. stepsimpl.
  autorewrite with push_nth. reflexivity.
Qed.
Hint Rewrite @step_sha256_compress using solve [eauto] : stepsimpl.

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
  cbv [SHA256.add_mod SHA256.w]. apply f_equal.
  cbv [SHA256.sigma1 SHA256.sigma0 SHA256.SHR].
  cbv [N.of_nat Pos.of_succ_nat Pos.succ]. clear.
  (* fully compute moduli *)
  repeat match goal with |- context [(_ mod ?m)%N] =>
                         progress compute_expr m end.
  (* convert to Z, solve with Z.div_mod_to_equations *)
  zify.
  repeat rewrite Z.rem_mod_nonneg; Z.div_mod_to_equations; lia.
Qed.
Hint Rewrite @step_sha256_message_schedule_update using solve [eauto] : stepsimpl.

Lemma step_sha256_round_constants (round : denote_type sha_round) :
  step sha256_round_constants tt (round, tt)
  = (tt, nth (N.to_nat round) SHA256.K 0%N).
Proof. reflexivity. Qed.
Hint Rewrite @step_sha256_round_constants using solve [eauto] : stepsimpl.

(* State invariant for sha256_inner *)
Definition sha256_inner_invariant
           (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
           msg (H : list N) (i : nat) : Prop :=
  let '(current_digest, (message_schedule, (done, round))) := state in
  if done
  then True (* idle; no guarantees about other state elements *)
  else
    (* the round is < 64 *)
    (round < 64)%N
    (* ...and the message schedule is the expected slice of the message *)
    /\ message_schedule = List.slice 0%N (SHA256.W msg i) (N.to_nat round - 15) 16
    (* ...and the current digest is the expected digest *)
    /\ current_digest = fold_left (SHA256.sha256_compress msg i)
                                 (seq 0 (N.to_nat round)) H.

(* Precondition for sha256_inner *)
Definition sha256_inner_pre
           (input : denote_type [Bit; sha_block; sha_digest; Bit])
           msg (i : nat) : Prop :=
  let '(block_valid, (block, (initial_digest, (clear,_)))) := input in
  (* if clear is true, then the message ghost variable is empty *)
  (if clear then msg = repeat x00 16 /\ i = 0%nat else True)
  (* ...and the initial digest is the digest from the previous i *)
  /\ initial_digest = fold_left (SHA256.sha256_step msg) (seq 0 i) SHA256.H0
  (* ...and if the block is valid, the block is the expected slice of the
     message *)
  /\ (if block_valid
     then block = List.slice 0%N (SHA256.W msg i) 0 16
     else True).

Definition sha256_inner_spec
           (input : denote_type [Bit; sha_block; sha_digest; Bit])
           (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
           msg (i : nat) : denote_type (sha_digest ** Bit) :=
  let '(block_valid, (block, (initial_digest, (clear,_)))) := input in
  let '(current_digest, (message_schedule, (done, round))) := state in
  let next_digest := if clear
                     then SHA256.H0
                     else if block_valid
                          then initial_digest
                          else if done
                               then current_digest
                               else SHA256.sha256_compress
                                      msg i (List.resize 0%N 8 current_digest)
                                      (N.to_nat round) in
  let next_done := if clear
                   then true
                   else if block_valid
                        then false
                        else if done
                             then true
                             else (round =? 63)%N in
  (List.map2 SHA256.add_mod (List.resize 0%N 8 initial_digest)
             (List.resize 0%N 8 next_digest), next_done).


Lemma step_sha256_inner_invariant
      (input : denote_type [Bit; sha_block; sha_digest; Bit])
      (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
      msg i :
  sha256_inner_pre input msg i ->
  sha256_inner_invariant state msg (fst (snd (snd input))) i ->
  sha256_inner_invariant
    (fst (step sha256_inner state input)) msg (fst (snd (snd input))) i.
Proof.
  destruct input as (block_valid, (block, (initial_digest, (clear, [])))).
  destruct state as (current_digest, (message_schedule, (done, round))).
  pose (t:=round). cbv [sha256_inner_invariant sha256_inner_pre].
  intros ? Hinv. logical_simplify. subst.
  cbv [sha256_inner K]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  (* destruct cases for [clear] *)
  destruct clear; logical_simplify; [ tauto | ].
  (* destruct cases for [block_valid] *)
  destruct block_valid; logical_simplify; subst;
    [ ssplit; auto; lia | ].
  (* destruct cases for [done] *)
  destruct done; logical_simplify; subst; boolsimpl; [ tauto | ].
  destr (round =? 63)%N; [ reflexivity | ].

  (* For remaining cases, the new [done] is always 0 *)
  cbn [N.lor N.eqb].
  (* destruct case statements *)
  repeat first [ discriminate
               | lia
               | destruct_one_match_hyp
               | destruct_one_match ].
  all:try (rewrite (N.mod_small _ (2 ^ N.of_nat 7))
            by (change (2 ^ N.of_nat 7)%N with 128%N; lia)).
  all:push_resize; push_nth.
  all:repeat match goal with
             | |- context [(?x <? ?y)] =>
               destr (x <? y); try lia; [ ]
             end.
  all:natsimpl.
  all:ssplit;
    lazymatch goal with
    | |- ?x = ?x => reflexivity
    | |- (_ < _)%N => lia
    | _ => idtac
    end.
  (* solve subgoals about compression *)
  all:
    lazymatch goal with
    | |- context [sha256_compress] =>
      erewrite step_sha256_compress with (t:=N.to_nat round) by (f_equal; lia);
        replace (N.to_nat (round + 1)) with (S (N.to_nat round)) by lia;
        cbn [fst snd]; pull_snoc; rewrite ?resize_noop by (symmetry; length_hammer);
          reflexivity
    | |- _ => idtac
    end.

  (* remaining subgoals should all be about message schedule: solve those *)
  all:lazymatch goal with
        | |- context [sha256_message_schedule_update] =>
          erewrite step_sha256_message_schedule_update with (t:=(N.to_nat round+1))
            by lazymatch goal with
               | |- nth _ _ _ = nth _ _ _ => f_equal; lia
               | _ => lia
               end; cbn [fst snd];
            lazymatch goal with
            | |- context [List.slice ?d ?ls ?start ?len ++ [nth ?n ?ls ?d]] =>
              replace n with (start + len) by lia
            end; rewrite slice_snoc, tl_slice; f_equal; lia
      end.
Qed.

Lemma step_sha256_inner
      (input : denote_type [Bit; sha_block; sha_digest; Bit])
      (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
      msg i :
  sha256_inner_pre input msg i ->
  sha256_inner_invariant state msg (fst (snd (snd input))) i ->
  snd (step sha256_inner state input) = sha256_inner_spec input state msg i.
Proof.
  destruct input as (block_valid, (block, (initial_digest, (clear, [])))).
  destruct state as (current_digest, (message_schedule, (done, round))).
  pose (t:=round). cbv [sha256_inner_invariant sha256_inner_pre sha256_inner_spec].
  intros. logical_simplify. subst. cbn [fst snd] in *.
  cbv [sha256_inner K]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  stepsimpl. push_resize.
  (* destruct cases for [clear] *)
  destruct clear; logical_simplify; subst;
    [ push_resize; reflexivity | ].
  (* destruct cases for [block_valid] *)
  destruct block_valid; logical_simplify; subst;
    [ push_resize; reflexivity | ].
  (* destruct cases for [done] *)
  destruct done; logical_simplify; subst; boolsimpl;
    [ destr (round =? 63)%N; repeat (f_equal; [ ]);
      push_resize; reflexivity | ].
  push_resize; push_nth.
  erewrite step_sha256_compress with (t:=N.to_nat round)
    by (repeat destruct_one_match;
        repeat destruct_one_match_hyp; f_equal; lia).
  cbn [fst snd]. push_resize. reflexivity.
Qed.
