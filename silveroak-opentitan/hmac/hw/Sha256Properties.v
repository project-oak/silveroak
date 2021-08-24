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
Require Import Cava.Util.BitArithmetic.
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

(* values of padder state constants *)
Definition padder_waiting_value : N := 0.
Definition padder_emit_bit_value : N := 1.
Definition padder_flushing_value : N := 2.
Definition padder_writing_length_value : N := 3.

(* Correctness for padder state constant circuits *)
Lemma step_padder_waiting : step padder_waiting tt tt = (tt, padder_waiting_value).
Proof. reflexivity. Qed.
Hint Rewrite @step_padder_waiting using solve [eauto] : stepsimpl.
Lemma step_padder_emit_bit : step padder_emit_bit tt tt = (tt, padder_emit_bit_value).
Proof. reflexivity. Qed.
Hint Rewrite @step_padder_emit_bit using solve [eauto] : stepsimpl.
Lemma step_padder_flushing : step padder_flushing tt tt = (tt, padder_flushing_value).
Proof. reflexivity. Qed.
Hint Rewrite @step_padder_flushing using solve [eauto] : stepsimpl.
Lemma step_padder_writing_length :
  step padder_writing_length tt tt = (tt, padder_writing_length_value).
Proof. reflexivity. Qed.
Hint Rewrite @step_padder_writing_length using solve [eauto] : stepsimpl.

(* State invariant for sha256_padder *)
Definition sha256_padder_invariant
           (state : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16))
           (msg : list Byte.byte) (word_index : nat) : Prop :=
  let '(done, (out, (out_valid, (state, (len, current_offset))))) := state in
  (* expected result as words *)
  let expected_words := SHA256.padded_msg msg in
  (* current offset matches word index *)
  current_offset = (N.of_nat word_index mod 16)%N
  (* ...and length matches the length of the message so far in bytes *)
  /\ (len = if (state =? padder_waiting_value)%N
           then N.of_nat (word_index * 4) (* still waiting on more data *)
           else N.of_nat (length msg))
  (* ...and state must be one of the 4 padder states *)
  /\ (state = padder_waiting_value
     \/ state = padder_emit_bit_value
     \/ state = padder_flushing_value
     \/ state = padder_writing_length_value)
  /\ (if done
     then
       (* if we're done, we must be in the padder_waiting state *)
       state = padder_waiting_value
       (* ...and the word index must be 0 *)
       /\ word_index = 0
     else
       (* if we're not done, the word index must be in range *)
       word_index < length expected_words).

(*
(* Maybe try a pure-gallina implementation as an intermediate step? *)

Definition bytes_in_final_word (msg : list Byte.byte) : nat :=
  let msg_words := BigEndianBytes.bytes_to_Ns 4 msg in
  length msg - ((length msg_words - 1) * 4).

Definition max_flushing_index (msg : list Byte.byte) : nat :=
  let msg_words := BigEndianBytes.bytes_to_Ns 4 msg in
  if bytes_in_final_word msg =? 4
  then
    (* need to allow an additional word for extra 1 bit *)
    if (length msg_words) mod 16 <? 12
    then length msg_words + (13 - ((length msg_words) mod 16 + 1))
    else length msg_words + 13 + ((16 - ((length msg_words) mod 16 + 1)))
  else
    (* extra 1 bit is part of final word *)
    if (length msg_words) mod 16 <? 13
    then length msg_words + (13 - ((length msg_words) mod 16 + 1))
    else length msg_words + 13 + ((16 - ((length msg_words) mod 16 + 1)))
  

Definition word_by_word_padder (msg : list Byte.byte) : list N :=
  let msg_words := BigEndianBytes.bytes_to_Ns 4 msg in
  List.map
    (fun i =>
       if i <? length msg_words - 1
       then nth i msg_words 0%N
       else if bytes_in_final_word msg =? 4
            then if i =? length msg_words - 1
                 then nth i msg_words 0%N (* last word *)
                 else if i =? length msg_words
                      then 0x80000000 (* extra bit *)
                      else if i 
            else if i =? length msg_words - 1
                 then BigEndianBytes.concat_bytes
                        (skipn (i*4) msg
                               ++ [Byte.x80]
                               ++ repeat Byte.x00 (3 - bytes_in_final_word))
                 else
              (* we're writing the 0s *)
              if i mod 16 =? 13
              then 
    )
    (seq 0 (length (SHA256.padded_msg msg))).

(* Need to add a clause that links state to word index
   < length msg -> padder_waiting
   > length padded_msg - 2 -> writing_length

   might need a proof demonstrating there is <= 1 block and > 2 words in between these, since we select on index...could be a pain

is there a simpler way to conceptualize what's happening?

can we define indices based on message that mark transitions?

max_msg_index = length (bytes_to_Ns msg) - 1
max_flushing_index = length padded_msg - 3
max_index = length padded_msg - 1

max_msg_index < max_index

max_msg_index < max_flushing_index
max_flushing_index mod 16 = 13
max_flishing_index - max_msg_index < 16


*)
*)
(* Precondition for sha256_padder *)
Definition sha256_padder_pre
           (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
           (state : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16))
           (msg : list Byte.byte) (word_index : nat) : Prop :=
  let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
  let '(done, (out, (out_valid, (state, (len, current_offset))))) := state in
  (* interpret message as words *)
  let msg_words := BigEndianBytes.bytes_to_Ns 4 msg in
  (* message length must be small enough that size in bits fits in a 64-bit word *)
  (N.of_nat (length msg) < 2 ^ 61)%N
  (* if clear is true, then the message ghost variable is empty *)
  /\ (if clear then msg = [] /\ word_index = 0%nat else True)
  (* the consumer should always be ready, unless the padder is done or the
     data is invalid *)
  /\ (if consumer_ready
     then True
     else
       data_valid = false /\ done = true)
  /\ (if data_valid
     then
       (* caller is only allowed to pass new valid data if we're in the
          padder_waiting state *)
       state = padder_waiting_value
       (* ...and the data must match the correct word of the message *)
       /\ data = nth word_index msg_words 0%N
       /\ (if is_final
          then
            (* if is_final is true, we must be at the last word index *)
            word_index = length msg_words - 1
            (* ...and the final length (expressed in bytes) must be correct *)
            /\ final_length = N.of_nat (length msg - ((length msg_words - 1) * 4))
          else
            (* if is_final is false, we must be at a word index that is in
               range and NOT the final word *)
            word_index < length msg_words - 1)
     else
       (* is_final must be false if data is not valid *)
       is_final = false
    ).

Definition sha256_padder_spec
           (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
           (state : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16))
           (msg : list Byte.byte) (word_index : nat) : denote_type (Bit ** sha_word ** Bit) :=
  let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
  let '(done, (out, (out_valid, (state, (len, current_offset))))) := state in
  (* expected result as words *)
  let expected_words := SHA256.padded_msg msg in
  let out_valid :=
      if clear
      then false
      else if consumer_ready
           then if done
                then data_valid (* we were previously done and got new valid data *)
                else 0 <? word_index (* we're partway through processing message *)
           else out_valid (* repeat last output if consumer is not ready *) in
  let out :=
      if clear
      then 0%N
      else if consumer_ready
           then nth word_index expected_words 0%N (* output matches expected value *)
           else out (* repeat last output if consumer is not ready *) in
  let done :=
      if clear
      then true
      else if consumer_ready
           then
             (* either this was the last word, or we were previously done and didn't
                start a new message this step *)
             ((word_index =? length expected_words - 1)
              || (done && negb data_valid))%bool
           else done (* stay in same state if consumer not ready *) in
  (out_valid, (out, done)).

(* TODO: move *)
Lemma step_bvresize {n m} (x : denote_type (BitVec n)) :
  step (bvresize (n:=n) m) tt (x, tt) = (tt, N.land x (N.ones (N.of_nat m))).
Proof. reflexivity. Qed.
Hint Rewrite @step_bvresize using solve [eauto] : stepsimpl.

(* TODO: move *)
Lemma length_bytes_to_Ns_upper_bound n bs :
  length (BigEndianBytes.bytes_to_Ns n bs) * n = length bs + n.
Admitted.
(* TODO: move *)
Lemma padded_message_longer_than_input msg :
  length (BigEndianBytes.bytes_to_Ns 4 msg) < length (SHA256.padded_msg msg).
Admitted.

(* Shorthand to calculate the new value of the [word_index] ghost variable for
   the padder *)
Definition padder_update_word_index
           (word_index : nat)
           (* new state *)
           (state : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16))
  : nat :=
  let '(done, (out, (out_valid, (state, (len, current_offset))))) := state in
  if done
  then 0
  else if out_valid
       then S word_index
       else word_index.

Lemma step_sha256_padder_invariant input state msg word_index :
  sha256_padder_pre input state msg word_index ->
  sha256_padder_invariant state msg word_index ->
  sha256_padder_invariant
    (fst (step sha256_padder state input)) msg
    (padder_update_word_index
       word_index (fst (step sha256_padder state input))).
Proof.
  (* keep track of the values of input and state so they're visible as we
     destruct cases; helps to figure out what case you're in when
     writing/debugging proofs *)
  pose (I:=input). pose (S:=state).
  destruct input as
      (data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,[])))))).
  destruct state as
      (done, (out, (out_valid, (state, (len, current_offset))))).
  (* simplify single-step behavior *)
  cbv [sha256_padder_pre sha256_padder_invariant padder_update_word_index].
  intros. logical_simplify. subst. cbn [fst snd] in *.
  cbv [sha256_padder K]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  stepsimpl.
  (* destruct cases for flags *)
  destruct clear;
    repeat (boolsimpl || subst || logical_simplify);
    (* handle case for clear=true *)
    [ ssplit; (lia || reflexivity || (cbn; tauto)) | ].
  destruct consumer_ready;
    repeat (boolsimpl || subst || logical_simplify);
    rewrite ?N.eqb_refl;
    (* handle case for consumer_ready=false *)
    [ | ssplit; (lia || reflexivity || (cbn; tauto)) ].
  destruct data_valid;
    repeat (boolsimpl || subst || logical_simplify);
    cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
               padder_emit_bit_value padder_writing_length_value].
  { (* Case for handling valid data:
       consumer_ready=true
       clear=false
       data_valid=true
     *)
    pose proof length_bytes_to_Ns_upper_bound 4 msg.
    pose proof padded_message_longer_than_input msg.
    ssplit.
    { (* offset matches word index *)
      compute_expr (2 ^ N.of_nat 4)%N.
      rewrite N.add_mod_idemp_l by lia.
      lia. }
    { (* length matches length processed so far *)
      rewrite N.land_ones.
      rewrite N.add_mod_idemp_r by (cbn;lia).
      compute_expr (2 ^ N.of_nat 61)%N.
      lazymatch goal with H : context [(2 ^ 61)%N] |- _ => cbn in H end.
      destruct is_final; rewrite ?N.eqb_refl;
        logical_simplify; subst;
          [ | rewrite N.mod_small; lia ].
      (* when is_final is true, we're never in the padder_waiting state *)
      lazymatch goal with
      | |- context [(?state =? padder_waiting_value)%N] =>
        replace (state =? padder_waiting_value)%N with false
          by (repeat destruct_one_match; reflexivity)
      end.
      rewrite N.mod_small; lia. }
    { (* state is one of the 4 allowed values *)
      repeat destruct_one_match; tauto. }
    { (* word index remains in range *)
      destruct is_final; logical_simplify; subst; lia. } }
  { (* Case for handling invalid date:
       consumer_ready=true
       clear=false
       data_valid=false
     *)
    ssplit.
    { (* offset matches word index *)
      cbv [padder_waiting_value padder_emit_bit_value padder_flushing_value
                                padder_writing_length_value] in *.
      destruct done; logical_simplify; subst; boolsimpl; [ reflexivity | ].
      compute_expr (2 ^ N.of_nat 4)%N. rewrite N.add_mod_idemp_l by lia.
      lazymatch goal with Hstate : state = _ \/ state = _ \/ state = _ \/ state = _ |- _ =>
                          destruct Hstate as [ ? | [? | [? | ?]]]; subst end;
        cbn [N.eqb Pos.eqb]; boolsimpl; try lia; [ ].
      repeat (destruct_one_match || destruct_one_match_hyp);
        Zify.zify; Z.to_euclidean_division_equations; lia. }
    { (* length matches length processed so far *)
      cbv [padder_waiting_value padder_emit_bit_value padder_flushing_value
                                padder_writing_length_value] in *.
      destruct done; logical_simplify; subst; boolsimpl; [ reflexivity | ].
      lazymatch goal with Hstate : state = _ \/ state = _ \/ state = _ \/ state = _ |- _ =>
                          destruct Hstate as [ ? | [? | [? | ?]]]; subst end;
        cbn [N.eqb Pos.eqb]; boolsimpl.
      all:repeat (destruct_one_match || destruct_one_match_hyp);
        Zify.zify; Z.to_euclidean_division_equations; lia. }
    { (* state is one of the 4 allowed values *)
      repeat destruct_one_match; tauto. }
    { (* word index remains in range *)
      cbv [padder_waiting_value padder_emit_bit_value padder_flushing_value
                                padder_writing_length_value] in *.
      destruct done; logical_simplify; subst; cbn [N.eqb Pos.eqb]; boolsimpl;
        [ ssplit; reflexivity | ].
      lazymatch goal with Hstate : state = _ \/ state = _ \/ state = _ \/ state = _ |- _ =>
                          destruct Hstate as [ ? | [? | [? | ?]]]; subst end;
        cbn [N.eqb Pos.eqb]; boolsimpl.
      all:try lia.
      Print SHA256.padding.
      (* state is emit_bit or flushing ->
         length msg_words <= word_index < length expected_words - 2
       *)
      (* to prove:
            - (length expected_words - 1) mod 16 = 15
            - if offset=13 and index > length msg_words, then index = length expected_words - 2
       *)
Admitted.

Lemma step_sha256_padder input state msg word_index :
  sha256_padder_pre input state msg word_index ->
  sha256_padder_invariant state msg word_index ->
  snd (step sha256_padder state input) = sha256_padder_spec input state msg word_index.
Proof.
  destruct input as
      (data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,[])))))).
  destruct state as
      (done, (out, (out_valid, (state, (len, current_offset))))).
  (* simplify single-step behavior *)
  cbv [sha256_padder_pre
         sha256_padder_invariant
         sha256_padder_spec
         padder_update_word_index].
  intros. logical_simplify. subst. cbn [fst snd] in *.
  cbv [sha256_padder K]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  stepsimpl.
  (* destruct cases for flags *)
  destruct clear;
    repeat (boolsimpl || subst || logical_simplify);
    (* handle case for clear=true *)
    [ reflexivity | ].
  destruct consumer_ready;
    repeat (boolsimpl || subst || logical_simplify);
    rewrite ?N.eqb_refl;
    (* handle case for consumer_ready=false *)
    [ | reflexivity ].
  destruct data_valid;
    repeat (boolsimpl || subst || logical_simplify);
    cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
               padder_emit_bit_value padder_writing_length_value].
  { (* case for valid data *)
Qed.
