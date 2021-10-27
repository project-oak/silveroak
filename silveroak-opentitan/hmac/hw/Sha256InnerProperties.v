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

Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.Byte.
Require Import Cava.Util.If.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Invariant.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import HmacSpec.SHA256Properties.
Require Import HmacHardware.Sha256.
Require HmacSpec.SHA256.
Import ListNotations.

Require Import coqutil.Tactics.autoforward.
Ltac autoforward_in db H ::=
  let tmp := fresh H in
  rename H into tmp;
  let A := type of tmp in
  pose proof ((ltac:(typeclasses eauto with db) : autoforward A _) tmp) as H;
  (* Recently, this `move` was added in coqutil, which breaks this proof script,
     because through destruct_one_match_hyp, it depends on the hypotheses order,
     and the most straightforward way to fix the broken proofs requires too
     much memory to work on CI *)
  (* move H after tmp; *)
  clear tmp.

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
      (k w : denote_type sha_word) (t : nat) (W : list N) :
  k = nth t SHA256.K 0%N ->
  w = nth t W 0%N ->
  step sha256_compress tt (H,(k,(w,tt)))
  = (tt, SHA256.sha256_compress W (List.resize 0%N 8 H) t).
Proof.
  intros. rewrite resize_map_nth. cbn [List.map seq].
  subst. cbv [sha256_compress]. stepsimpl.
  autorewrite with push_nth. reflexivity.
Qed.
Hint Rewrite @step_sha256_compress using solve [eauto] : stepsimpl.

Lemma step_sha256_message_schedule_update
      (w0 w1 w9 w14 : denote_type sha_word) (t i : nat) msg :
  w0 = nth (t-16) (SHA256Alt.W msg i) 0%N ->
  w1 = nth (t-15) (SHA256Alt.W msg i) 0%N ->
  w9 = nth (t-7) (SHA256Alt.W msg i) 0%N ->
  w14 = nth (t-2) (SHA256Alt.W msg i) 0%N ->
  (16 <= t < 64) ->
  step sha256_message_schedule_update tt (w0, (w1, (w9, (w14, tt))))
  = (tt, nth t (SHA256Alt.W msg i) 0%N).
Proof.
  intros. cbv [sha256_message_schedule_update]. stepsimpl.
  rewrite nth_W_alt by lia. destruct_one_match; [ lia | ].
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

(* High-level representation for sha256_inner:
   msg : message seen so far (padded)
   i : block index
   t : round number (compression loop)
   inner_done : whether the computation for the current block is complete
   cleared : boolean indicating whether the circuit has been cleared
 *)
Instance sha256_inner_invariant
  : invariant_for sha256_inner (list N * nat * nat * bool * bool) :=
  fun (state : denote_type (sha_digest ** sha_block ** Bit ** sha_round))
    repr =>
    let '(current_digest, (message_schedule, (done, round))) := state in
    let '(msg, i, t, inner_done, cleared) := repr in
    (* inner_done matches the [done] bit *)
    inner_done = done
    (* ...and if we've been cleared, then we're in the reset state *)
    /\ (if cleared
       then current_digest = SHA256.H0
            /\ done = true
            /\ t = 0
            /\ i = 0
            /\ msg = []
       else
         (* ...if we're not cleared, the current digest is the expected digest *)
         let initial_digest :=
             fold_left (SHA256Alt.sha256_step msg) (seq 0 i) SHA256.H0 in
         current_digest = fold_left (SHA256.sha256_compress (SHA256Alt.W msg i))
                                    (seq 0 t) initial_digest
         (* ...and the message has (S i) blocks (1 block = 16 words) *)
         /\ S i * 16 = length msg
      )
    /\ if done
      then if cleared then t = 0 else t = 64
      else
        (* the round is < 64 *)
        (round < 64)%N
        (* ...and inner_round matches [round] *)
        /\ t = N.to_nat round
        (* ...and the message schedule is the expected slice of the message *)
        /\ message_schedule = List.slice 0%N (SHA256Alt.W msg i) (t - 15) 16.

Instance sha256_inner_specification
  : specification_for sha256_inner (list N * nat * nat * bool * bool) :=
  {| reset_repr := ([], 0%nat, 0%nat, true, true);
     update_repr :=
       fun (input : denote_type [Bit; sha_block; sha_digest; Bit])
         repr =>
         let '(block_valid, (block, (initial_digest, (clear,_)))) := input in
         let '(msg, i, t, inner_done, cleared) := repr in
         let updated_msg := msg ++ block in
         if clear
         then ([], 0%nat, 0%nat, true, true)
         else if inner_done
              then if block_valid
                   then if cleared
                        then
                          (* start with i=0 *)
                          (updated_msg, 0, 0, false, false)
                        else
                          (* starting new block *)
                          (updated_msg, S i, 0, false, false)
                   else
                     (* unchanged *)
                     (msg, i, t, inner_done, cleared)
              else (msg, i, S t, t =? 63, false);
     precondition :=
       fun (input : denote_type [Bit; sha_block; sha_digest; Bit])
         repr =>
         let '(block_valid, (block, (initial_digest, (clear,_)))) := input in
         let '(msg, i, t, inner_done, cleared) := repr in
         if block_valid
         then
           let new_i := if cleared then 0 else S i in
           (* a valid block is passed only if we're not busy *)
           inner_done = true
           (* ...and the initial digest is the digest up to (the new value of) i *)
           /\ initial_digest = fold_left (SHA256Alt.sha256_step (msg ++ block))
                                        (seq 0 new_i) SHA256.H0
           (* and the length of the block is 16 *)
           /\ length block = 16
         else
           if inner_done
           then True (* no requirements; stay in the done state until block is valid *)
           else
             (* the initial digest is the digest up to i *)
             initial_digest = fold_left (SHA256Alt.sha256_step msg)
                                        (seq 0 i) SHA256.H0;
     postcondition :=
       fun (input : denote_type [Bit; sha_block; sha_digest; Bit])
         repr (output : denote_type (sha_digest ** Bit)) =>
         let '(block_valid, (block, (initial_digest, (clear,_)))) := input in
         let '(msg, i, t, inner_done, cleared) := repr in
         let new_done := if clear
                         then true
                         else if block_valid
                              then false
                              else if inner_done
                                   then true
                                   else t =? 63 in
         exists output_value : denote_type sha_digest,
           output = (output_value, new_done)
           /\ (* the output value is only meaningful in the case when we're done and not
                cleared *)
           (if cleared
            then True (* no guarantees *)
            else if clear
                 then True (* no guarantees *)
                 else if new_done
                      then
                        (* if the initial digest is correct, the output value
                           matches the expected digest *)
                        initial_digest = fold_left (SHA256Alt.sha256_step msg) (seq 0 i) SHA256.H0 ->
                        output_value = fold_left (SHA256Alt.sha256_step msg) (seq 0 (S i)) SHA256.H0
                      else True (* no guarantees *))
  |}.

Lemma sha256_inner_invariant_at_reset : invariant_at_reset sha256_inner.
Proof.
  simplify_invariant sha256_inner.
  cbn [reset_state reset_repr sha256_inner sha256_inner_specification];
    stepsimpl.
  ssplit; reflexivity.
Qed.

Lemma sha256_inner_invariant_preserved : invariant_preserved sha256_inner.
Proof.
  simplify_invariant sha256_inner. cbn [absorb_any].
  simplify_spec sha256_inner.
  intros (block_valid, (block, (initial_digest, (clear, [])))).
  intros (current_digest, (message_schedule, (done, round))).
  intros ((((msg, i), t), inner_done), cleared).
  intros; logical_simplify; subst.
  cbv [sha256_inner K]. cbn [negb]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  (* destruct cases for [clear] *)
  destruct clear; logical_simplify; [ tauto | ].
  (* destruct cases for [block_valid] *)
  destruct block_valid; logical_simplify; subst;
    [ destruct cleared; logical_simplify; subst;
      pull_snoc; natsimpl; push_length;
      rewrite ?slice0_W_alt by length_hammer;
      ssplit; (lia || reflexivity) | ].
  (* destruct cases for [done] *)
  destruct done; logical_simplify; subst; boolsimpl;
    [ ssplit; auto; tauto | ].
  (* destruct cases for [cleared] *)
  destruct cleared; logical_simplify; subst; boolsimpl;
    [ destr (round =? 63)%N;
      ssplit; repeat destruct_one_match; lia | ].
  destr (N.to_nat round =? 63);
    (destr (round =? 63)%N; try lia; [ ]); subst;
      [ ssplit; lazymatch goal with
                | |- context [sha256_compress] => idtac
                | |- _ => lia
                end;
      (* handle case involving last compression step *)
      subst; destruct_one_match; try lia; [ ];
      erewrite step_sha256_compress with (t:=63)
      by (push_resize; push_nth; reflexivity);
      cbn [fst snd]; push_resize;
      rewrite seq_snoc with (len:=63); rewrite fold_left_app;
      reflexivity | ].

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
             | |- context [(?x =? ?y)] =>
               destr (x =? y); try lia; [ ]
             end.
  all:natsimpl.
  all:ssplit;
    lazymatch goal with
    | |- ?x = ?x => reflexivity
    | |- (_ < _)%N => lia
    | |- @eq nat _ _ => length_hammer
    | |- True => tauto
    | _ => idtac
    end.
  (* solve subgoals about compression *)
  all:
    lazymatch goal with
    | |- context [sha256_compress] =>
      erewrite step_sha256_compress with (t:=N.to_nat round) by (f_equal; lia);
        cbn [fst snd]; pull_snoc; rewrite ?resize_noop by (symmetry; length_hammer);
          try reflexivity
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

Lemma sha256_inner_output_correct : output_correct sha256_inner.
Proof.
  simplify_invariant sha256_inner. cbn [absorb_any].
  simplify_spec sha256_inner.
  intros (block_valid, (block, (initial_digest, (clear, [])))).
  intros (current_digest, (message_schedule, (done, round))).
  intros ((((msg, i), t), inner_done), cleared).
  intros. logical_simplify. subst. cbn [fst snd] in *.
  cbv [sha256_inner K]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  stepsimpl. push_resize.
  (* some general-purpose simplification *)
  pull_snoc; natsimpl.
  eexists. ssplit; [ | ].
  { apply f_equal2; [ reflexivity | ].
    (* prove that done bit matches spec *)
    boolsimpl. destr clear;[ reflexivity | ].
    destr block_valid; [ reflexivity | ].
    destr done; boolsimpl; [ reflexivity | ].
    logical_simplify; subst.
    destr (N.to_nat round =? 63); destr (round =? 63)%N; lia. }
  (* destruct cases for [cleared] *)
  destruct cleared; logical_simplify; subst; [ tauto | ].
  (* destruct cases for [clear] *)
  destruct clear; logical_simplify; subst; [ tauto | ].
  (* destruct cases for [block_valid] *)
  destruct block_valid; logical_simplify; subst;
    [ push_resize; rewrite ?resize_noop by (symmetry; length_hammer);
      try reflexivity | ].
  (* destruct cases for [done] *)
  destruct done; logical_simplify; subst; boolsimpl;
    [ intros; subst; rewrite !resize_noop by (symmetry; length_hammer);
      reflexivity | ].
  push_resize; push_nth.
  erewrite step_sha256_compress with (t:=N.to_nat round)
    by (repeat destruct_one_match;
        repeat destruct_one_match_hyp; f_equal; lia).
  cbn [fst snd]. push_resize.
  rewrite ?resize_noop by (symmetry; length_hammer).
  destr (N.to_nat round =? 63); destr (round =? 63)%N; try lia; [ ].
  intros; subst. unfold SHA256Alt.sha256_step.
  rewrite seq_snoc with (len:=63); rewrite fold_left_app.
  reflexivity.
Qed.

Existing Instances sha256_inner_invariant_at_reset sha256_inner_invariant_preserved
         sha256_inner_output_correct.
Global Instance sha256_inner_correctness : correctness_for sha256_inner.
Proof. constructor; typeclasses eauto. Defined.
