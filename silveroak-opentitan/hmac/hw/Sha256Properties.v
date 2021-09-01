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

Inductive padder_state :=
| WAITING
| EMIT_BIT
| PADDING
| WRITING_LENGTH
.

Definition word_by_word_padder
           (state : padder_state) (length : nat) (offset : nat)
           (data_valid : bool) (data : N) (is_final : bool) (final_length : nat)
  : (bool * N) * (padder_state * nat * nat) :=
  let next_state :=
      match state with
      | WAITING =>
        if is_final
        then if final_length =? 4
             then EMIT_BIT
             else if offset =? 13
                  then WRITING_LENGTH
                  else FLUSHING
        else WAITING
      | EMIT_BIT => if offset =? 13
                   then WRITING_LENGTH
                   else FLUSHING
      | FLUSHING => 
      if is_final && state == `padder_waiting` then
        (* From our receiving state we can transition to: *)
        (* - Emitting 0x80.. state if final word was a full word *)
        if final_length == `K 4` then `padder_emit_bit`
        (* - Writing length directly if we there 2 words left in this block *)
        else if current_offset == `K 13`
          then `padder_writing_length`
          (* - Writing padding 0's *)
          else `padder_flushing`
        else if state == `padder_emit_bit` then
          `padder_flushing`
        else if state == `padder_flushing` then
          (* If we are at offset 13, switch to writing length as there is space
             this block for the length *)
          if current_offset == `K 13`
          then `padder_writing_length`
          else `padder_flushing`
        else if state == `padder_writing_length` then
          if current_offset == `K 15`
          then `padder_waiting`
          else `padder_writing_length`
        else
          state
        in

      let next_length :=
        if state == `padder_waiting` && is_final then length + `bvresize 61` final_length
        else if state == `padder_waiting` && data_valid then length + `K 4`
        (* We are done here so set the next length to 0 *)
        else if state == `padder_writing_length` && current_offset == `K 15`
          then `K 0`
        else length
        in

      let next_out :=
        (* If we have final word and its not a full word, we can emit 0x80 byte
         * immediately *)
        if state == `padder_waiting` && is_final then
          if final_length == `K 0`
          then `Constant (BitVec 32) 0x80000000`
          else if final_length == `K 1`
          then `bvconcat` (`bvslice 24 8` data) (`Constant (BitVec 24) 0x800000`)
          else if final_length == `K 2`
          then `bvconcat` (`bvslice 16 16` data) (`Constant (BitVec 16) 0x8000`)
          else if final_length == `K 3`
          then `bvconcat` (`bvslice 8 24` data) (`Constant (BitVec 8) 0x80`)
          else data
        else if state == `padder_waiting` && data_valid then
          data
        else if state == `padder_emit_bit` then
          `Constant (BitVec 32) 0x80000000`
        else if state == `padder_writing_length` then
          if current_offset == `K 14`
          then `bvslice 32 32` (length << 3)
          else `bvslice 0 32` (length << 3)

        else `K 0`
      in

      let out_valid :=
        !(state == `padder_waiting` && (!data_valid) && (!is_final) ) in

      let next_offset :=
        if !out_valid then current_offset
        else (current_offset + `K 1`) (* addition mod 16 *) in

      let next_done :=
        !data_valid && (
        done || (state == `padder_writing_length` && next_state == `padder_waiting`)) in

      ( next_done
      , next_out, out_valid, next_state, next_length, next_offset)

      initially
        (true,(0,(false,(0,(0,0)))))
        : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 4)
        in

    (out_valid, out, done)

Definition expected_padder_state
           (msg : list Byte.byte) (msg_complete : bool) (i : nat) : N :=
  if msg_complete
  then if i =? length msg
       then padder_emit_bit_value
       else
         (* check if message ends early enough for length to fit in same
            block (block=64 bytes, length=8 bytes, 64-8=56) *)
         if (length msg + 1) mod 64 <? 56
         then if 56 <=? i mod 64
              then padder_writing_length_value
              else padder_flushing_value
         else if i <? length msg + 8
              then padder_flushing_value
              else if 56 <=? i mod 64
                   then padder_writing_length_value
                   else padder_flushing_value
  else padder_waiting_value.

(* State invariant for sha256_padder *)
Definition sha256_padder_invariant
           (state : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16))
           (msg : list Byte.byte) (msg_complete padder_done : bool) (index : nat) : Prop :=
  let '(done, (out, (out_valid, (state, (len, current_offset))))) := state in
  (* index is always a multiple of 4 *)
  index mod 4 = 0
  (* ...and offset is always in the range [0,15] *)
  /\ (0 <= current_offset < 16)%N
  (* ...and the [padder_done] ghost variable just tracks [done] *)
  /\ done = padder_done
  /\ (if out_valid
     then
       (* if output is valid, we must have processed at least one word *)
       4 <= index
       (* ...and the output must match the spec *)
       /\ out = BigEndianBytes.concat_bytes
                 (firstn 4 (skipn (index - 4) (SHA256.padded_msg_bytes msg)))
     else True)
  /\ (if done
     then
       (* if we're done, we must be in the padder_waiting state *)
       state = padder_waiting_value
       (* ...and if the output is valid, the index must be at the end of the
          expected result *)
       /\ (if out_valid
          then index = length (SHA256.padded_msg_bytes msg)
          else index = 0 /\ msg = [])
       (* ...and length is 0 *)
       /\ len = N.of_nat 0
     else
       (* if we're not done, the word index must be in range *)
       index < length (SHA256.padded_msg_bytes msg)
       (* ...and length matches the length of the message so far in bytes *)
       /\ len = N.of_nat (length msg)
       (* ...and the current offset matches index *)
       /\ (current_offset * 4 = N.of_nat index mod 64)%N
       (* ...and the state must match the message and word index *)
       /\ state = expected_padder_state msg msg_complete index).

(* Precondition for sha256_padder *)
Definition sha256_padder_pre
           (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
           (msg : list Byte.byte) (msg_complete padder_done : bool) (index : nat) : Prop :=
  let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
  (* message length, plus any new data, must be small enough that size in bits
     fits in a 64-bit word *)
  (if data_valid
   then if is_final
        then (N.of_nat (length msg) + final_length < 2 ^ 61)%N
        else (N.of_nat (length msg) + 4 < 2 ^ 61)%N
   else (N.of_nat (length msg) < 2 ^ 61)%N)
  (* ...and if clear is true, then the message ghost variable is empty *)
  /\ (if clear then msg = [] /\ index = 0 else True)
  /\ (if data_valid
     then
       (* caller is only allowed to pass new valid data if we're in the
          padder_waiting state *)
       expected_padder_state msg msg_complete index = padder_waiting_value
       (* ...and the message is complete iff is_final is true *)
       /\ msg_complete = is_final
       /\ (if is_final
          then
            (* if this is the final word, and the message must have
               [final_length] additional bytes beyond what was already
               processed *)
            length msg = index + N.to_nat final_length
            (* ...and final_length must be in the range [1,4] *)
            /\ 1 <= N.to_nat final_length <= 4
          else
            (* if this is not the final word, the message must have exactly 4
               additional bytes beyond what was already processed *)
            length msg = index + 4)
     else
       (* is_final must be false if data is not valid *)
       is_final = false
    ).

Definition sha256_padder_spec
           (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
           (state : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16))
           (msg : list Byte.byte) (msg_complete padder_done : bool) (index : nat)
  : denote_type (Bit ** sha_word ** Bit) :=
  let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
  let '(done, (out, (out_valid, (state, (len, current_offset))))) := state in
  (* expected result as words *)
  let expected_words := SHA256.padded_msg msg in
  let word_index := index / 4 in
  let out_valid :=
      if clear
      then false
      else if consumer_ready
           then if padder_done
                then data_valid (* we were previously done and got new valid data *)
                else 0 <? word_index (* we're partway through processing message *)
           else false (* dummy output if consumer is not ready *) in
  let out :=
      if clear
      then 0%N
      else if consumer_ready
           then nth word_index expected_words 0%N (* output matches expected value *)
           else 0%N (* dummy output if consumer is not ready *) in
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
Lemma length_N_to_bytes n bs :
  length (BigEndianBytes.N_to_bytes n bs) = n.
Admitted.
Hint Rewrite @length_N_to_bytes : push_length.
(* TODO: move *)
Lemma length_bytes_to_Ns_upper_bound n bs :
  length (BigEndianBytes.bytes_to_Ns n bs) * n < length bs + n.
Admitted.
(* TODO: move *)
Lemma padded_message_bytes_longer_than_input msg :
  length msg < length (SHA256.padded_msg_bytes msg).
Admitted.
Lemma padded_message_longer_than_input msg :
  length (BigEndianBytes.bytes_to_Ns 4 msg) < length (SHA256.padded_msg msg).
Admitted.
(* TODO: move *)
Lemma padded_message_bytes_min_length msg :
  64 <= length (SHA256.padded_msg_bytes msg).
Admitted.
(* TODO: move *)
Lemma padded_message_min_length msg : 16 <= length (SHA256.padded_msg msg).
Admitted.
(* TODO: move *)
(* Adding data cannot decrease padded message size *)
Lemma padded_message_bytes_length_mono msg data :
  length (SHA256.padded_msg_bytes msg) <=
  length (SHA256.padded_msg_bytes (msg ++ data)).
Admitted.

(* Shorthand to calculate the new value of the [index] ghost variable for the
   padder *)
Definition padder_update_index
           (msg : list Byte.byte) (msg_complete padder_done : bool) (index : nat)
           (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
  : nat :=
  let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
  if clear
  then 0
  else if consumer_ready
       then if padder_done
            then if data_valid
                 then 4
                 else 0
            else if msg_complete
                 then index + 4
                 else if data_valid
                      then index + 4
                      else index
       else index.

(* Shorthand to calculate the new value of the [msg] ghost variable for the
   padder *)
Definition padder_update_msg
           (msg : list Byte.byte) (msg_complete padder_done : bool) (index : nat)
           (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
  : list Byte.byte :=
  let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
  if clear
  then []
  else if consumer_ready
       then if padder_done
            then if data_valid
                 then BigEndianBytes.N_to_bytes 4 data
                 else []
            else if data_valid
                 then msg ++ BigEndianBytes.N_to_bytes 4 data
                 else msg
       else msg.

(* Shorthand to calculate the new value of the [msg_complete] ghost variable for the
   padder *)
Definition padder_update_msg_complete
           (msg : list Byte.byte) (msg_complete padder_done : bool) (index : nat)
           (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
  : bool :=
  let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
  if clear
  then false
  else if consumer_ready
       then if data_valid
            then is_final
            else msg_complete
       else msg_complete.

(* Shorthand to calculate the new value of the [padder_done] ghost variable for the
   padder *)
Definition padder_update_padder_done
           (msg : list Byte.byte) (msg_complete padder_done : bool) (index : nat)
           (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
  : bool :=
  let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
  let new_index := padder_update_index msg msg_complete padder_done index input in
  let new_msg := padder_update_msg msg msg_complete padder_done index input in
  if clear
  then true
  else if consumer_ready
       then if padder_done
            then negb data_valid
            else new_index =? length (SHA256.padded_msg_bytes new_msg)
       else padder_done.

Lemma step_sha256_padder_invariant input state msg msg_complete padder_done index :
  sha256_padder_pre input msg msg_complete padder_done index ->
  sha256_padder_invariant state msg msg_complete padder_done index ->
  sha256_padder_invariant
    (fst (step sha256_padder state input))
    (padder_update_msg msg msg_complete padder_done index input)
    (padder_update_msg_complete msg msg_complete padder_done index input)
    (padder_update_padder_done msg msg_complete padder_done index input)
    (padder_update_index msg msg_complete padder_done index input).
Proof.
  (* keep track of the values of input and state so they're visible as we
     destruct cases; helps to figure out what case you're in when
     writing/debugging proofs *)
  pose (I:=input). pose (S:=state). pose (mc:=msg_complete).
  destruct input as
      (data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,[])))))).
  destruct state as
      (done, (out, (out_valid, (state, (len, current_offset))))).
  (* simplify single-step behavior *)
  cbv [sha256_padder_pre sha256_padder_invariant
                         padder_update_msg
                         padder_update_msg_complete
                         padder_update_padder_done
                         padder_update_index].
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
    pose proof padded_message_bytes_longer_than_input msg.
    pose proof padded_message_bytes_min_length msg.
    let data := lazymatch goal with |- context [msg ++ ?data] => data end in
    pose proof padded_message_bytes_length_mono msg data;
    pose proof padded_message_bytes_min_length data.
    ssplit.
    { (* index is a multiple of 4 *)
      repeat destruct_one_match;
        rewrite ?Nat.mod_add with (b:=1) (c:=4); auto. }
    { (* offset stays in range *)
      change (2 ^ N.of_nat 4)%N with 16%N.
      apply N.mod_bound_pos; lia. }
    { (* offset stays in range *)
      change (2 ^ N.of_nat 4)%N with 16%N.
      apply N.mod_bound_pos; lia. }
    { (* padder_done matches done *)
      repeat destruct_one_match; [ reflexivity | | ];
      logical_simplify; subst.
      all:symmetry; apply Nat.eqb_neq.
      all:let data := lazymatch goal with |- context [?msg ++ ?data] => data end in
          pose proof padded_message_bytes_longer_than_input (msg ++ data).
      all:autorewrite with push_length in *; lia. }
    { (* if output is valid, then new index must be at least 4 *)
      repeat destruct_one_match; lia. }
    { (* output matches spec *)
      admit. }
    { cbv [expected_padder_state] in *.
      destruct padder_done, out_valid, is_final; logical_simplify; subst.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:repeat destruct_one_match; lia. }
    { (* length matches length processed so far *)
      rewrite N.land_ones.
      rewrite N.add_mod_idemp_r by (cbn;lia).
      compute_expr (2 ^ N.of_nat 61)%N.
      lazymatch goal with H : context [(2 ^ 61)%N] |- _ => cbn in H end.
      cbv [expected_padder_state] in *.
      destruct is_final; logical_simplify; subst; boolsimpl.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:logical_simplify; subst; cbn [length app] in *.
      all:rewrite ?N.eqb_refl; try lia.
      all:push_length.
      all:rewrite N.mod_small; lia. }
    { (* new offset matches expectations *)
      cbv [expected_padder_state] in *. change (2 ^ N.of_nat 4)%N with 16%N.
      destruct padder_done, out_valid, is_final; logical_simplify; subst.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:cbn [length app] in *.
      all:repeat destruct_one_match; try lia.
      all:admit.
      (* modular arithmetic, proof sketch:
         Given: offset * 4 = index mod 64
         Prove: (offset + 1) mod 16 * 4 = (index + 4) mod 64

         (index + 4) mod 64 (RHS)
         = (index mod 64 + 4) mod 64
         = (offset * 4 + 4) mod 64
         = ((offset + 1) * 4) mod 64
         (now easier to think in terms of bitwise representations)
         = ((offset + 1) << 2) & N.ones 6
         = ((offset + 1) & N.ones 4) << 2
         (back to numeric)
         = (offset + 1) mod 16 * 4 (LHS)
       *)
    }
    { (* new state matches expectation *)
      cbv [expected_padder_state] in *.
      destruct padder_done, out_valid, is_final;
        logical_simplify; subst; rewrite ?N.eqb_refl; boolsimpl.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:repeat destruct_one_match; try discriminate; reflexivity. } }
  { (* Case for handling invalid data:
       consumer_ready=true
       clear=false
       data_valid=false
     *)
    pose proof length_bytes_to_Ns_upper_bound 4 msg.
    pose proof padded_message_longer_than_input msg.
    pose proof padded_message_bytes_longer_than_input msg.
    pose proof padded_message_bytes_min_length msg.
    ssplit.
    { (* index is a multiple of 4 *)
      repeat destruct_one_match;
        rewrite ?Nat.mod_add with (b:=1) (c:=4); auto. }
    { (* offset stays in range *)
      change (2 ^ N.of_nat 4)%N with 16%N.
      destruct_one_match;
        try apply N.mod_bound_pos; lia. }
    { (* offset stays in range *)
      change (2 ^ N.of_nat 4)%N with 16%N.
      destruct_one_match;
        try apply N.mod_bound_pos; lia. }
    { (* padder_done matches done *)
      destruct padder_done; logical_simplify; subst; [ reflexivity | ].
      boolsimpl.
      admit. (* prove that looking for writing_length state and offset = 13 is
                the same as waiting for the end of the expected message *)
    }
    { (* if output is valid, then new index must be at least 4 and output must
         match spec *)
      destr (state =? padder_waiting_value)%N; boolsimpl; [ solve [trivial] | ].
      split.
      { (* new index is at least 4 *)
        repeat destruct_one_match; logical_simplify; subst; try lia;
          cbv [expected_padder_state] in *; repeat destruct_one_match_hyp;
            congruence. }
      { (* output matches spec *)
        admit. } }
    { (* new state matches expectation *)
      assert (expected_padder_state msg msg_complete index = padder_waiting_value
              \/ expected_padder_state msg msg_complete index = padder_emit_bit_value
              \/ expected_padder_state msg msg_complete index = padder_flushing_value
              \/ expected_padder_state msg msg_complete index = padder_writing_length_value)
             as padder_state_cases by admit.
      destruct padder_done;
        logical_simplify; subst; rewrite ?N.eqb_refl;
          cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
                     padder_emit_bit_value padder_writing_length_value
                     negb andb orb];
          [ ssplit; reflexivity | ].
      let H := fresh in
      destruct padder_state_cases as [H|[H|[H|H]]]; rewrite H in *.
      all:cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
                     padder_emit_bit_value padder_writing_length_value
                     negb andb orb].
      all:repeat (first [ progress boolsimpl_hyps
                        | destruct_one_match
                        | destruct_one_match_hyp];
                  try discriminate).
      all:logical_simplify; subst.
      all:ssplit; try lia.

      (*
        if the value is padder_waiting, we must be done

        I think the difficulty here stems from mismatch between expected_padder_state case analysis and the actual circuit.
       *)

  } }





































  
    { (* length matches length processed so far *)
      pose (pd:=padder_done).
      destruct padder_done; logical_simplify; subst.
      all:repeat destruct_one_match; cbn [length].
      all:repeat lazymatch goal with
                 | H : (_ && _)%bool = true |- _ =>
                   apply Bool.andb_true_iff in H
                 | H : (_ && _)%bool = false |- _ =>
                   apply Bool.andb_false_iff in H; destruct H
                 end.
      all:logical_simplify; N.bool_to_prop; subst.
      all:ssplit.
      all:try discriminate; try reflexivity.
      {
        (* In this case, padder is done and we just got some non-valid
        data. Therefore, ghost vars should reset; message should become 0. Why
        is length in circuit still length of message? Does it not reset?

        Ah, looking at circuit, length resets when done=true, so base this
        requirement on done

         *)
        

        
        
      all:
      N.bool_to_prop; subst.
      destruct padder_done; logical_simplify; subst; [ discriminate | ].
      cbv [expected_padder_state] in *.
      repeat (destruct_one_match_hyp; try discriminate).
      all:logical_simplify; subst; lia. }
    { destruct padder_done; logical_simplify; subst; boolsimpl;
        cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
                   padder_emit_bit_value padder_writing_length_value
                   andb orb negb].
      {
        (* in this condition, we're done and *next* out_valid is false (why?) *)
        (* done=true, data_valid=false, is_final=false, state=padder_waiting
           index should not be incremented if we're done, ever
         *)
        destruct out_valid; logical_simplify; subst.
        all: ssplit; [ reflexivity | | ].
        (*
          out_valid:
                !(state == `padder_waiting` && (!data_valid) && (!is_final) )

          new state should still be padder_waiting
          data_valid=false, is_final=false
          therefore new out_valid should be false...
         *)
        all: repeat destruct_one_match; try lia.
        

      cbv [expected_padder_state] in *.
      destruct done, out_valid, msg_complete; logical_simplify; subst.
      all:cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
                     padder_emit_bit_value padder_writing_length_value
                     andb orb negb].
      all:ssplit; try reflexivity.
      all:repeat destruct_one_match.
    }

































  
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
