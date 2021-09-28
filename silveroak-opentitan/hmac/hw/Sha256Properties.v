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
           if cleared
           then True (* no requirements *)
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
         (* the output is only meaningful in the case when we're done and not
            cleared *)
         if cleared
         then True (* no guarantees *)
         else if clear
              then True (* no guarantees *)
              else if new_done
                   then
                     (* output value matches expected digest *)
                     output = (fold_left (SHA256Alt.sha256_step msg) (seq 0 (S i)) SHA256.H0, true)
                   else True (* no guarantees *)
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
    [ rewrite !resize_noop by (symmetry; length_hammer);
      reflexivity | ].
  push_resize; push_nth.
  erewrite step_sha256_compress with (t:=N.to_nat round)
    by (repeat destruct_one_match;
        repeat destruct_one_match_hyp; f_equal; lia).
  cbn [fst snd]. push_resize.
  rewrite ?resize_noop by (symmetry; length_hammer).
  destr (N.to_nat round =? 63); destr (round =? 63)%N; try lia; [ ].
  subst. apply f_equal2; [ | reflexivity ].
  unfold SHA256Alt.sha256_step.
  rewrite seq_snoc with (len:=63); rewrite fold_left_app.
  reflexivity.
Qed.

Existing Instances sha256_inner_invariant_at_reset sha256_inner_invariant_preserved
         sha256_inner_output_correct.
Global Instance sha256_inner_correctness : correctness_for sha256_inner.
Proof. constructor; typeclasses eauto. Defined.

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

Definition expected_padder_state
           (msg : list Byte.byte) (msg_complete padder_done : bool) (i : nat) : N :=
  if msg_complete
  then if padder_done
       then padder_waiting_value
       else if i =? length msg
            then padder_emit_bit_value
            else
              (* check if message ends early enough for length to fit in same
                 block (block=64 bytes, length=8 bytes, 64-8=56) *)
              if (length msg + 1) mod 64 <=? 56
              then if 56 <=? i mod 64
                   then padder_writing_length_value
                   else padder_flushing_value
              else if i <? length msg + 9
                   then padder_flushing_value
                   else if 56 <=? i mod 64
                        then padder_writing_length_value
                        else padder_flushing_value
  else padder_waiting_value.

(* Higher-level state for padder :
   msg : message so far
   msg_complete : whether message is complete
   padder_done : whether computation for this message is done
   index : index (in bytes) of the padded message we're currently working on
*)
Instance sha256_padder_invariant
  : invariant_for sha256_padder (list byte * bool * bool * nat) :=
  fun (state : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16))
    repr =>
    let '(done, (out, (out_valid, (state, (len, current_offset))))) := state in
    let '(msg, msg_complete, padder_done, index) := repr in
    (* index is always a multiple of 4 *)
    index mod 4 = 0
    (* ...and offset is always in the range [0,15] *)
    /\ (0 <= current_offset < 16)%N
    (* ...and the [padder_done] ghost variable just tracks [done] *)
    /\ done = padder_done
    (* ...and if msg_complete is true, we must have processed the whole message *)
    /\ (if msg_complete then length msg <= index else index = length msg)
    (* ...and if we're in the emit_bit state, it must be the case that the message
     length is 0 mod 4 (otherwise we attach the 1 bit to the final byte and move
     straight to flushing) *)
    /\ (if (state =? padder_emit_bit_value)%N then length msg mod 4 = 0 else True)
    /\ (if done
       then
         (* if we're done, we must be in the padder_waiting state *)
         state = padder_waiting_value
         (* ...and length is 0 *)
         /\ len = N.of_nat 0
         (* ...and offset is 0 *)
         /\ current_offset = N.of_nat 0
       else
         (* if we're not done, the word index must be in range *)
         index < padded_message_size msg
         (* ...and length matches the length of the message so far in bytes *)
         /\ len = N.of_nat (length msg)
         (* ...and the current offset matches index *)
         /\ (current_offset * 4 = N.of_nat index mod 64)%N
         (* ...and the state must match the message and word index *)
         /\ state = expected_padder_state msg msg_complete padder_done index).

(* Convenience definition: get any valid bytes from the input *)
Definition new_msg_bytes (data_valid : bool) (data : N) (is_final : bool) (final_length : N)
  : list byte :=
  if data_valid
  then if is_final
       then firstn (N.to_nat final_length) (BigEndianBytes.N_to_bytes 4 data)
       else BigEndianBytes.N_to_bytes 4 data
  else [].

Instance sha256_padder_specification
  : specification_for sha256_padder (list byte * bool * bool * nat) :=
  {| reset_repr := ([], false, true, 0%nat);
     update_repr :=
       fun (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
         repr =>
         let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
         let '(msg, msg_complete, padder_done, index) := repr in
         let new_bytes := new_msg_bytes data_valid data is_final final_length in
         if clear
         then ([], false, true, 0)
         else if consumer_ready
              then if padder_done
                   then if data_valid
                        then (new_bytes, is_final, false, 4)
                        else (msg, msg_complete, padder_done, index) (* stay in the same state *)
                   else if msg_complete
                        then if index + 4 =? padded_message_size msg
                             then (msg, true, true, index + 4)
                             else (msg, true, false, index + 4)
                        else if data_valid
                             then (msg ++ new_bytes, is_final, false, index + 4)
                             else (msg, false, false, index)
              else (msg, msg_complete, padder_done, index) (* stay in the same state *);
     precondition :=
       fun (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
         repr =>
         let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
         let '(msg, msg_complete, padder_done, index) := repr in
         let new_bytes := new_msg_bytes data_valid data is_final final_length in
         (* the total message length (including any new data) cannot exceed 2 ^
            64 bits (2^61 bytes) -- using N so Coq doesn't try to compute 2 ^ 61
            in nat *)
         (N.of_nat (length (msg ++ new_bytes)) < 2 ^ 61)%N
         /\ (if data_valid
            then
              (* if data is valid, the message must not be complete *)
              msg_complete = false
              (* ...and final_length (if given) must be in range *)
              /\ (if is_final
                 then (1 <= final_length <= 4)%N
                 else True)
                (* ...and data value must be in range *)
              /\ (if is_final
                 then data < 2 ^ (8 * final_length)
                 else data < 2 ^ 32)%N
            else True
           );
     postcondition :=
       fun (input : denote_type [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit])
         repr (output : denote_type (Bit ** sha_word ** Bit)) =>
         let '(data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,_)))))) := input in
         let '(msg, msg_complete, padder_done, index) := repr in
         let new_bytes := new_msg_bytes data_valid data is_final final_length in
         (* update value of message *)
         let new_msg := if clear
                        then []
                        else if consumer_ready
                             then if padder_done
                                  then if data_valid
                                       then new_bytes
                                       else msg
                                  else if msg_complete
                                       then msg
                                       else if data_valid
                                            then msg ++ new_bytes
                                            else msg
                             else msg in
         (* updated value of index *)
         let new_index := if clear
                          then 0
                          else if consumer_ready
                               then if padder_done
                                    then if data_valid
                                         then 4
                                         else index
                                    else if msg_complete
                                         then index + 4
                                         else if data_valid
                                              then index + 4
                                              else index
                               else index in
         (* expected result as words *)
         let expected_words := SHA256.padded_msg new_msg in
         let word_index := (new_index - 4) / 4 in
         if consumer_ready
         then
           exists out_value,
             (* out_valid can be determined based on the flags in the input and state *)
             let out_valid :=
                 if clear
                 then false
                 else if padder_done
                      then data_valid (* valid only if we got new valid data *)
                      else if msg_complete
                           then true (* message is done, produce valid output always *)
                           else data_valid (* we're partway through processing message *) in
             (* so can the [done] bit (this should simply match update_repr) *)
             let out_done :=
                 if clear
                 then true
                 else if padder_done
                      then negb data_valid
                      else if msg_complete
                           then index + 4 =? padded_message_size msg
                           else false in
             (* equation for output *)
             output = (out_valid, (out_value, out_done))
             (* if output is valid, the value matches expected output data *)
             /\ (if out_valid
                then out_value = nth word_index expected_words 0%N
                else True)
         else True (* no guarantees about output if consumer isn't ready *)
  |}.

Lemma sha256_padder_invariant_at_reset : invariant_at_reset sha256_padder.
Proof.
  simplify_invariant sha256_padder.
  cbn [reset_state reset_repr sha256_padder sha256_padder_specification];
    stepsimpl.
  ssplit; reflexivity.
Qed.

(* helper lemma for modular arithmetic *)
Lemma increment_offset (offset index : N) :
  (offset * 4 = index mod 64)%N ->
  ((offset + 1) mod 16 * 4 = (index + 4) mod 64)%N.
Proof. intros. prove_by_zify. Qed.

Local Ltac padder_state_simpl :=
  cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
             padder_emit_bit_value padder_writing_length_value
             negb andb orb] in *.

Lemma expected_padder_state_cases msg (msg_complete padder_done : bool) index :
  index < padded_message_size msg ->
  index mod 4 = 0 ->
  (if msg_complete then length msg <= index else index = length msg) ->
  ( (* either we're in the waiting state and the padder's expected output at
       index i is just the ith byte of the message *)
    (expected_padder_state msg msg_complete padder_done index = padder_waiting_value
     /\ (if msg_complete then padder_done = true else True))
    (* ...or we're in the emit_bit state and the padder's expected output at
       index i is 0x80 *)
    \/ (expected_padder_state msg msg_complete padder_done index = padder_emit_bit_value
       /\ msg_complete = true
       /\ padder_done = false
       /\ index = length msg
       /\ index < padded_message_size msg - 8)
    (* ...or we're in the flushing state and the padder's expected output at
       index i is 0x00 *)
    \/ (expected_padder_state msg msg_complete padder_done index = padder_flushing_value
       /\ msg_complete = true
       /\ padder_done = false
       /\ length msg < index < padded_message_size msg - 8)
    (* ...or we're in the writing_length state and the padder's expected output
       at index i part of the length *)
    \/ (expected_padder_state msg msg_complete padder_done index = padder_writing_length_value
       /\ msg_complete = true
       /\ padder_done = false
       /\ padded_message_size msg - 8 <= index)).
Proof.
  intros.
  pose proof padded_message_bytes_longer_than_input msg.
  pose proof padded_message_size_modulo msg.
  assert (padded_message_size msg - 64 < length msg + 9 <= padded_message_size msg).
  { apply Nat.ceiling_range; lia. }
  (* helpful assertion for the case that length fits in the same block as
     message *)
  assert ((length msg + 1) mod 64 <= 56 ->
          padded_message_size msg - 64 <= length msg + 1).
  { cbv [padded_message_size] in *. intros.
    replace (length msg + 9) with (length msg + 1 + 8) by lia.
    rewrite Nat.ceiling_add_same with (c:=8) by lia.
    pose proof Nat.ceiling_range (length msg + 1 + 1) 64 ltac:(lia) ltac:(lia).
    lia. }
  (* helpful assertion for the case that length does not fit in the same block
     as message *)
  assert (56 < (length msg + 1) mod 64 ->
          padded_message_size msg - 64 >= length msg + 1).
  { cbv [padded_message_size] in *. intros.
    replace (length msg + 9) with (length msg + 1 + 8) by lia.
    rewrite Nat.ceiling_add_diff with (c:=8) by lia.
    pose proof Nat.ceiling_range (length msg + 1) 64 ltac:(lia) ltac:(lia).
    lia. }
  cbv [expected_padder_state]; repeat destruct_one_match; subst; try lia;
    padder_state_simpl.
  all:repeat lazymatch goal with
             | |- ?P \/ ?Q =>
               first [ let H := fresh in
                       assert (~ P) as H by (intro; logical_simplify; discriminate);
                       clear H; right
                     | left ]
             end.
  all:ssplit; try reflexivity; try lia.
  (* solve all other goals with modular arithmetic automation *)
  all:prove_by_zify.
Qed.

Lemma sha256_padder_invariant_preserved : invariant_preserved sha256_padder.
Proof.
  simplify_invariant sha256_padder. cbn [absorb_any].
  simplify_spec sha256_padder.
  intros input state. intros (((msg,msg_complete),padder_done),index).
  (* keep track of the values of input and state so they're visible as we
     destruct cases; helps to figure out what case you're in when
     writing/debugging proofs *)
  pose (I:=input). pose (S:=state). pose (mc:=msg_complete).
  destruct input as
      (data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,[])))))).
  destruct state as
      (done, (out, (out_valid, (state, (len, current_offset))))).
  intros; logical_simplify; subst. cbv [new_msg_bytes].
  intros. logical_simplify. subst. cbn [fst snd] in *.
  cbv [sha256_padder K]. stepsimpl.
  repeat (destruct_inner_pair_let; cbn [fst snd]).
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
    padder_state_simpl.
  { (* Case for handling valid data:
       consumer_ready=true
       clear=false
       data_valid=true
     *)
    pose proof padded_message_bytes_longer_than_input msg.
    pose proof min_padded_message_size msg.
    lazymatch goal with
    | |- context [firstn ?n (BigEndianBytes.N_to_bytes 4 ?data)] =>
      let data := constr:(BigEndianBytes.N_to_bytes 4 data) in
      pose proof padded_message_size_mono msg (firstn n data);
        pose proof padded_message_size_mono msg data;
        pose proof min_padded_message_size (firstn n data);
        pose proof min_padded_message_size data
    end.
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
      repeat destruct_one_match; reflexivity. }
    { (* index is past or at end of message if is_final is true, otherwise equal
         to length of message *)
      repeat destruct_one_match; logical_simplify; subst; push_length; lia. }
    { (* if we're in the emit_bit state, then the length of the message was 0
         mod 4 *)
      cbv [expected_padder_state] in *.
      destruct padder_done, out_valid, is_final; logical_simplify; subst;
        boolsimpl; padder_state_simpl.
      all:lazymatch goal with
          | H : context [new_msg_bytes] |- _ =>
            cbv [new_msg_bytes] in H; autorewrite with push_length in H;
              try rewrite Min.min_l in H by lia
          end.
      all:repeat first [ discriminate | destruct_one_match | destruct_one_match_hyp ].
      all:subst; try tauto.
      all:push_length; natsimpl.
      all:prove_by_zify. }
    { cbv [expected_padder_state] in *.
      destruct padder_done, out_valid, is_final; logical_simplify; subst.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:repeat destruct_one_match; lia. }
    { (* length matches length processed so far *)
      rewrite N.land_ones.
      rewrite N.add_mod_idemp_r by (cbn;lia).
      cbv [expected_padder_state] in *.
      compute_expr (N.of_nat 61).
      destruct is_final; logical_simplify; subst; boolsimpl.
      all:lazymatch goal with
          | H : context [length (?msg ++ new_msg_bytes _ _ _ _)] |- _ =>
            cbv [new_msg_bytes] in H;
              autorewrite with push_length in H;
              try rewrite Min.min_l in H by lia
          end.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:logical_simplify; subst; cbn [length app] in *.
      all:rewrite ?N.eqb_refl; try lia.
      all:push_length; natsimpl.
      all:rewrite N.mod_small; lia. }
    { (* new offset matches expectations *)
      cbv [expected_padder_state] in *. change (2 ^ N.of_nat 4)%N with 16%N.
      destruct padder_done, out_valid, is_final; logical_simplify; subst.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:cbn [length app] in *.
      all:repeat destruct_one_match; try lia.
      all:rewrite ?Nat2N.inj_add.
      all:change (N.of_nat 4 mod 64)%N with ((0 + N.of_nat 4) mod 64)%N.
      all:apply increment_offset; auto. }
    { (* new state matches expectation *)
      pose proof increment_offset current_offset (N.of_nat (length msg)) as Hincr.
      (* assert that N and nat computations are equivalent *)
      assert (N.to_nat ((N.of_nat (length msg) + 4) mod 64) = (length msg + 4) mod 64)
        by (clear; prove_by_zify).
      cbv [expected_padder_state] in *.
      destruct padder_done, out_valid, is_final;
        logical_simplify; subst; rewrite ?N.eqb_refl; boolsimpl.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:autorewrite with push_length.
      all:rewrite ?Min.min_l by lia.
      all:rewrite ?Nat.mod_small by lia.
      all:repeat (destruct_one_match; try discriminate; try lia); subst.
      all:try (specialize (Hincr ltac:(assumption)); cbn in Hincr).
      all:try lia; prove_by_zify. } }
  { (* Case for handling invalid data:
       consumer_ready=true
       clear=false
       data_valid=false
     *)
    pose proof padded_message_bytes_longer_than_input msg.
    pose proof min_padded_message_size msg.
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
      pose proof padded_message_size_modulo msg.
      pose proof
           expected_padder_state_cases msg msg_complete false index
           ltac:(eauto) ltac:(eauto) ltac:(eauto) as padder_state_cases.
      let H := fresh in
      destruct padder_state_cases as [H|[H|[H|H]]];
        logical_simplify; subst;
        lazymatch goal with H : expected_padder_state _ _ _ _ = _ |- _ =>
                            rewrite H in * end.
      all:padder_state_simpl.
      all:try (destruct msg_complete; try discriminate).
      all:repeat lazymatch goal with
                 | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                 | |- context [N.eqb ?x ?y] => destr (N.eqb x y); try lia
                 | H : context [Nat.eqb ?x ?y] |- _ => destr (Nat.eqb x y); try lia
                 | H : context [N.eqb ?x ?y] |- _ => destr (N.eqb x y); try lia
                 end.
      all:boolsimpl_hyps.
      all:try congruence.
      all:try discriminate.
      all:prove_by_zify. }
    { (* if message is complete, index is past or at end of message; otherwise,
         index = length of message *)
      repeat destruct_one_match; logical_simplify; subst; push_length; lia. }
    { (* if state is emit_bit, length of message is 0 mod 4 *)
      destruct padder_done; logical_simplify; subst;
      rewrite ?N.eqb_refl in *; boolsimpl; padder_state_simpl;
      [ destruct is_final; padder_state_simpl;
        repeat destruct_one_match; tauto | ].
      pose proof
           expected_padder_state_cases msg msg_complete false index
           ltac:(eauto) ltac:(eauto) ltac:(eauto) as padder_state_cases.
      let H := fresh in
      destruct padder_state_cases as [H|[H|[H|H]]];
        logical_simplify; subst;
        lazymatch goal with H : expected_padder_state _ _ _ _ = _ |- _ =>
                            rewrite H in * end.
      all:padder_state_simpl; boolsimpl.
      all:repeat
            first [ discriminate
                  | tauto
                  | destruct_one_match; subst
                  | destruct_one_match_hyp; subst
                  ]. }
    { (* entire clause for what happens if we're done or not done *)
      destruct padder_done;
      logical_simplify; subst; rewrite ?N.eqb_refl; padder_state_simpl;
      [ ssplit; reflexivity | ].
      pose proof
           expected_padder_state_cases msg msg_complete false index
           ltac:(eauto) ltac:(eauto) ltac:(eauto) as padder_state_cases.
      let H := fresh in
      destruct padder_state_cases as [H|[H|[H|H]]];
        logical_simplify; subst;
        lazymatch goal with H : expected_padder_state _ _ _ _ = _ |- _ =>
                            rewrite H in * end.
      all:padder_state_simpl.
      all:repeat lazymatch goal with
                 | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia; [ ]
                 end.
      { (* padder_waiting case *)
        repeat destruct_one_match; try discriminate; ssplit; lia. }
      { (* padder_emit_bit case *)
        pose proof padded_message_size_modulo msg.
        ssplit; [ lia .. | | ].
        { rewrite Nat2N.inj_add. apply increment_offset; lia. }
        { cbv [expected_padder_state].
          repeat destruct_one_match; try reflexivity; try discriminate.
          all:prove_by_zify. } }
      { (* padder_flushing case *)
        pose proof padded_message_size_modulo msg.
        ssplit; [ lia .. | | ].
        { rewrite Nat2N.inj_add.
          apply increment_offset; lia. }
        { cbv [expected_padder_state] in *.
          repeat destruct_one_match; try reflexivity; try discriminate.
          all:try prove_by_zify.
          all:repeat destruct_one_match_hyp; prove_by_zify. } }
      { (* padder_writing_length case *)
        pose proof padded_message_size_modulo msg.
        assert (if (current_offset =? 15)%N
                then index = padded_message_size msg - 4
                else current_offset = 14%N /\ index = padded_message_size msg - 8)
          by (destruct_one_match; prove_by_zify).
        destr (current_offset =? 15)%N;
          logical_simplify; subst; padder_state_simpl.
        { repeat destruct_one_match; try lia; [ ].
          ssplit; reflexivity. }
        { repeat destruct_one_match; try lia; [ ].
          ssplit; [ lia .. | | ].
          { rewrite Nat2N.inj_add.
            apply increment_offset; lia. }
          { repeat lazymatch goal with
                   | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia; [ ]
                   end.
            assert ((padded_message_size msg - 4) mod 64 = 60) by prove_by_zify.
            replace (padded_message_size msg - 8 + 4) with (padded_message_size msg - 4) by lia.
            cbv [expected_padder_state] in *.
            repeat first [ destruct_one_match | destruct_one_match_hyp | lia ]. }
  } } } }
Qed.

Local Ltac testbit_crush :=
  repeat lazymatch goal with
         | |- context [N.eqb ?x ?y] => destr (N.eqb x y); try lia; subst
         | |- N.testbit ?x _ = N.testbit ?x _ => f_equal; lia
         | _ => first [ progress (push_Ntestbit; boolsimpl) | reflexivity ]
         end.

Lemma sha256_padder_output_correct : output_correct sha256_padder.
Proof.
  simplify_invariant sha256_padder. cbn [absorb_any].
  simplify_spec sha256_padder.
  intros input state. intros (((msg,msg_complete),padder_done),index).
  (* keep track of the values of input and state so they're visible as we
     destruct cases; helps to figure out what case you're in when
     writing/debugging proofs *)
  pose (I:=input). pose (S:=state). pose (mc:=msg_complete).
  destruct input as
      (data_valid, (data, (is_final, (final_length, (consumer_ready, (clear,[])))))).
  destruct state as
      (done, (out, (out_valid, (state, (len, current_offset))))).
  intros; logical_simplify; subst. cbv [new_msg_bytes].
  cbv [sha256_padder K]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  (* destruct cases for flags *)
  destruct clear;
    repeat (boolsimpl || subst || logical_simplify);
    (* handle case for clear=true *)
    [ repeat destruct_one_match;
      eexists ;ssplit; (lia || reflexivity) | ].
  destruct consumer_ready;
    repeat (boolsimpl || subst || logical_simplify);
    rewrite ?N.eqb_refl;
    (* handle case for consumer_ready=false *)
    [ | eexists; ssplit; (lia || reflexivity) ].
  destruct data_valid;
    repeat (boolsimpl || subst || logical_simplify);
    padder_state_simpl.
  { (* data_valid=true *)
    pose proof padded_message_bytes_longer_than_input msg.
    pose proof min_padded_message_size msg.
    lazymatch goal with
    | |- context [firstn ?n (BigEndianBytes.N_to_bytes 4 ?data)] =>
      let data := constr:(BigEndianBytes.N_to_bytes 4 data) in
      pose proof padded_message_size_mono msg (firstn n data);
        pose proof padded_message_size_mono msg data;
        pose proof min_padded_message_size (firstn n data);
        pose proof min_padded_message_size data;
        pose proof padded_message_bytes_longer_than_input (msg ++ firstn n data);
        pose proof padded_message_size_modulo (msg ++ firstn n data)
    end.
    lazymatch goal with
    | H : context [expected_padder_state ?msg ?mc ?pd ?i] |- _ =>
      pose proof
           expected_padder_state_cases msg mc pd i
           ltac:(lia) ltac:(eauto) ltac:(cbn;lia)
        as padder_state_cases
    end.
    let H := fresh in
    destruct padder_state_cases as [H|[H|[H|H]]];
      logical_simplify; subst;
        lazymatch goal with H : expected_padder_state _ _ _ _ = _ |- _ =>
                            rewrite H in * end;
        padder_state_simpl;
        (* there should be only one case, since valid data means we have to be
           in the padder_waiting state *)
        try discriminate; [ ].
    destruct padder_done;
      logical_simplify; subst; rewrite ?N.eqb_refl;
        padder_state_simpl.
    { (* padder_done=true *)
      autorewrite with push_length in *. compute_expr (0 / 4).
      destruct is_final.
      { (* padder_done=true, is_final=true *)
        compute_expr (N.of_nat 16).
        compute_expr (N.of_nat (16 + 16)).
        change 32768%N with (2 ^ 15)%N.
        change 8388608%N with (2 ^ 23)%N.
        change 128%N with (2 ^ 7)%N.
        (* solve the boolean parts of the tuple *)
        eexists; split; [ reflexivity | ].
        repeat destruct_one_match; subst; try lia.
        all:
          try lazymatch goal with
              | H1 : ?final_length <> 1%N,
                     H2 : ?final_length <> 2%N,
                          H3 : ?final_length <> 3%N |- _ =>
                assert (final_length = 4%N) by lia; subst
              end.
        all:cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
        all:lazymatch goal with
            | H : (?data < 2 ^ ?n)%N |- context [?data] =>
              replace data with (N.land data (N.ones n))
                by (rewrite N.land_ones; apply N.mod_small; lia)
            end.
        all:rewrite nth_padded_msg.
        all:change ((4 - 4) / 4)%nat with 0%nat.
        all:cbn [Nat.mul Nat.add].
        all:cbv [BigEndianBytes.N_to_bytes]; cbn [seq List.map firstn].
        all:cbn [Nat.sub Nat.mul N.of_nat Pos.of_succ_nat
                         Pos.succ N.mul Pos.mul Pos.add].
        all:cbv [SHA256.padded_msg_bytes]; cbn [app nth].
        all:lazymatch goal with
            | |- context [SHA256.padding ?msg] =>
              compute_expr (SHA256.padding msg); cbn [app nth]
            | _ => idtac
            end.
        all:cbv [BigEndianBytes.concat_bytes]; cbn [fold_left].
        all:rewrite !N_to_byte_to_N; cbn [Byte.to_N].
        all:change 128%N with (2 ^ 7)%N.
        all:rewrite <-!N.land_ones with (n:=8%N).
        all:apply N.bits_inj; intro i.
        all:push_Ntestbit; boolsimpl.
        all:destr (i <? 8)%N; testbit_crush.
        all:destr (i <? 16)%N; testbit_crush.
        all:destr (i <? 24)%N; testbit_crush.
        all:destr (i <? 32)%N; testbit_crush. }
      { (* padder_done=true, is_final=false *)
        (* solve the boolean parts of the tuple *)
        eexists; split; [ reflexivity | ].
        all:lazymatch goal with
            | H : (?data < 2 ^ ?n)%N |- context [?data] =>
              replace data with (N.land data (N.ones n))
                by (rewrite N.land_ones; apply N.mod_small; lia)
            end.
        rewrite nth_padded_msg.
        change ((4 - 4) / 4)%nat with 0%nat.
        cbn [Nat.mul Nat.add].
        cbv [BigEndianBytes.N_to_bytes]; cbn [seq List.map firstn].
        cbn [Nat.sub Nat.mul N.of_nat Pos.of_succ_nat
                     Pos.succ N.mul Pos.mul Pos.add].
        cbv [SHA256.padded_msg_bytes]; cbn [app nth].
        cbv [BigEndianBytes.concat_bytes]; cbn [fold_left].
        rewrite !N_to_byte_to_N; cbn [Byte.to_N].
        rewrite <-!N.land_ones with (n:=8%N).
        apply N.bits_inj; intro i.
        push_Ntestbit; boolsimpl.
        destr (i <? 8)%N; testbit_crush.
        destr (i <? 16)%N; testbit_crush.
        destr (i <? 24)%N; testbit_crush.
        destr (i <? 32)%N; testbit_crush. } }
    { (* padder_done=false *)
      destruct is_final.
      { (* padder_done=false, is_final=true *)
        cbn [Nat.add].
        compute_expr (N.of_nat 8).
        compute_expr (N.of_nat 16).
        compute_expr (N.of_nat 24).
        compute_expr (N.of_nat 32).
        change 32768%N with (2 ^ 15)%N.
        change 8388608%N with (2 ^ 23)%N.
        change 128%N with (2 ^ 7)%N.
        (* solve the boolean parts of the tuple *)
        eexists; split; [ reflexivity | ].
        rewrite nth_padded_msg. natsimpl.
        rewrite Nat.mul_div_exact_r by lia.
        cbv [SHA256.padded_msg_bytes].
        rewrite !app_assoc_reverse. push_nth. natsimpl.
        autorewrite with push_length in *.
        repeat destruct_one_match; subst; try lia.
        all:
          try lazymatch goal with
              | H1 : ?final_length <> 1%N,
                     H2 : ?final_length <> 2%N,
                          H3 : ?final_length <> 3%N |- _ =>
                assert (final_length = 4%N) by lia; subst
              end.
        all:lazymatch goal with
            | |- context [firstn (N.to_nat ?n)] =>
              compute_expr (N.to_nat n) end.
        all:cbn [N.to_nat] in *; cbv [Pos.to_nat Pos.iter_op] in *.
        all:cbn [Nat.mul Nat.add] in *.
        all:push_nth; push_length; natsimpl.
        all:repeat lazymatch goal with
                   | |- context [nth _ (_ ++ _)] =>
                     rewrite app_nth1 by (length_hammer || push_length; prove_by_zify)
                   end.
        all:cbn [Nat.ltb Nat.leb].
        all:push_nth.
        all:lazymatch goal with
            | H : (?data < 2 ^ ?n)%N |- context [?data] =>
              replace data with (N.land data (N.ones n))
                by (rewrite N.land_ones; apply N.mod_small; lia)
            end.
        all:cbv [BigEndianBytes.N_to_bytes]; cbn [seq List.map firstn].
        all:cbn [Nat.sub Nat.mul N.of_nat Pos.of_succ_nat
                         Pos.succ N.mul Pos.mul Pos.add].
        all:push_nth.
        all:cbv [BigEndianBytes.concat_bytes]; cbn [fold_left].
        all:rewrite !N_to_byte_to_N; cbn [Byte.to_N].
        all:change 128%N with (2 ^ 7)%N.
        all:rewrite <-!N.land_ones with (n:=8%N).
        all:apply N.bits_inj; intro i.
        all:push_Ntestbit; boolsimpl.
        all:destr (i <? 8)%N; testbit_crush.
        all:destr (i <? 16)%N; testbit_crush.
        all:destr (i <? 24)%N; testbit_crush.
        all:destr (i <? 32)%N; testbit_crush. }
      { (* padder_done=false, is_final=false *)
        (* solve the boolean parts of the tuple *)
        eexists; split; [ reflexivity | ].
        rewrite nth_padded_msg. natsimpl.
        rewrite Nat.mul_div_exact_r by lia.
        cbv [SHA256.padded_msg_bytes].
        rewrite !app_assoc_reverse. push_nth. natsimpl.
        lazymatch goal with
        | H : (?data < 2 ^ ?n)%N |- context [?data] =>
          replace data with (N.land data (N.ones n))
            by (rewrite N.land_ones; apply N.mod_small; lia)
        end.
        autorewrite with push_length in *.
        cbn [Nat.mul Nat.add].
        cbv [BigEndianBytes.N_to_bytes]; cbn [seq List.map firstn].
        cbn [Nat.sub Nat.mul N.of_nat Pos.of_succ_nat
                     Pos.succ N.mul Pos.mul Pos.add].
        cbv [SHA256.padded_msg_bytes]; cbn [app nth].
        cbv [BigEndianBytes.concat_bytes]; cbn [fold_left].
        rewrite !N_to_byte_to_N; cbn [Byte.to_N].
        rewrite <-!N.land_ones with (n:=8%N).
        apply N.bits_inj; intro i.
        push_Ntestbit; boolsimpl.
        destr (i <? 8)%N; testbit_crush.
        destr (i <? 16)%N; testbit_crush.
        destr (i <? 24)%N; testbit_crush.
        destr (i <? 32)%N; testbit_crush. } } }
  { (* data_valid=false *)
    pose proof padded_message_bytes_longer_than_input msg.
    pose proof min_padded_message_size msg.
    pose proof padded_message_size_modulo msg.
    destruct padder_done;
      logical_simplify; subst; rewrite ?N.eqb_refl;
        padder_state_simpl; boolsimpl;
          (* solve padder_done=true case *)
          [ eexists; split; reflexivity | ].
    lazymatch goal with
    | |- context [expected_padder_state ?msg ?mc ?pd ?i] =>
      pose proof
           expected_padder_state_cases msg mc pd i
           ltac:(lia) ltac:(eauto) ltac:(eauto)
        as padder_state_cases
    end.
    let H := fresh in
    destruct padder_state_cases as [H|[H|[H|H]]];
      logical_simplify; subst;
        lazymatch goal with H : expected_padder_state _ _ _ _ = _ |- _ =>
                            rewrite H in * end;
        rewrite ?N.eqb_refl in *; padder_state_simpl.
    { (* state=padder_waiting *)
      destruct msg_complete; logical_simplify; subst; [ discriminate | ].
      eexists; split; reflexivity. }
    { (* state=padder_emit_bit *)
      eexists; split; [ | reflexivity ].
      do 2 f_equal;
      [ | symmetry; apply Nat.eqb_neq; push_length; prove_by_zify ].
      rewrite nth_padded_msg. natsimpl. rewrite Nat.mul_div_exact_r by lia.
      cbv [SHA256.padded_msg_bytes]. push_nth. natsimpl. listsimpl.
      rewrite !app_nth1 by (push_length; prove_by_zify).
      natsimpl. push_nth. reflexivity. }
    { (* state=padder_flushing *)
      eexists; split; [ | reflexivity ].
      do 2 f_equal;
      [ | symmetry; apply Nat.eqb_neq; push_length; prove_by_zify ].
      rewrite nth_padded_msg. natsimpl. rewrite Nat.mul_div_exact_r by lia.
      cbv [SHA256.padded_msg_bytes]. push_nth. natsimpl. listsimpl.
      rewrite !app_nth1 by (push_length; prove_by_zify).
      rewrite !nth_padding_nonzero by lia.
      reflexivity. }
    { (* state=writing_length *)
      push_length.
      eexists; split; [ | reflexivity ].
      do 2 f_equal;
        [ |
          repeat lazymatch goal with
                 | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                 | |- context [N.eqb ?x ?y] => destr (N.eqb x y); try lia
                 | H : context [Nat.eqb ?x ?y] |- _ => destr (Nat.eqb x y); try lia
                 | H : context [N.eqb ?x ?y] |- _ => destr (N.eqb x y); try lia
                 end;
          try discriminate; prove_by_zify ].
      rewrite nth_padded_msg. natsimpl. rewrite Nat.mul_div_exact_r by lia.
      cbv [SHA256.padded_msg_bytes]. listsimpl. push_nth.
      push_length. natsimpl.
      rewrite !nth_N_to_bytes by (push_length; prove_by_zify).
      replace (SHA256.l msg) with (N.shiftl (N.of_nat (length msg)) 3)
        by apply N.shiftl_mul_pow2.
      (* helpful assertion for length truncation *)
      assert (2 ^ 61 * 8 = 2 ^ 64)%N by reflexivity.
      rewrite !N.land_ones with (n:=64%N).
      all:lazymatch goal with
          | H : context [new_msg_bytes] |- _ =>
            cbv [new_msg_bytes] in H; autorewrite with push_length in H
          end.
      rewrite (N.mod_small (N.of_nat (length msg)) (2^64)%N) by lia.
      rewrite (N.mod_small (N.shiftl (N.of_nat (length msg)) _) (2^64)%N)
        by (rewrite N.shiftl_mul_pow2; change (2 ^ N.of_nat 3)%N with 8%N;
            lia).
      rewrite <-!N.land_ones.
      assert (if (current_offset =? 15)%N
              then index = padded_message_size msg - 4
              else current_offset = 14%N /\ index = padded_message_size msg - 8)
          by (destruct_one_match; prove_by_zify).
        destr (current_offset =? 15)%N;
          logical_simplify; subst; padder_state_simpl.
        all:cbv [BigEndianBytes.concat_bytes]; cbn [fold_left].
        all:rewrite !N_to_byte_to_N; cbn [Byte.to_N].
        all:rewrite <-!N.land_ones with (n:=8%N).
        all:apply N.bits_inj; intro i.
        all:push_Ntestbit; boolsimpl.
        all:push_length.
        all:change (N.of_nat 0) with 0%N; rewrite ?N.add_0_r.
        all:change (N.of_nat 3) with 3%N.
        all:destr (i <? 8)%N; testbit_crush.
        all:destr (i <? 16)%N; testbit_crush.
        all:destr (i <? 24)%N; testbit_crush.
        all:destr (i <? 32)%N; testbit_crush. } }
Qed.

Existing Instances sha256_padder_invariant_at_reset sha256_padder_invariant_preserved
         sha256_padder_output_correct.
Global Instance sha256_padder_correctness : correctness_for sha256_padder.
Proof. constructor; typeclasses eauto. Defined.

(* Higher-level representation for sha256:
   msg : message so far
   msg_complete : whether the message is complete
   byte_index : index indicating the last byte the padder has gotten to
   t : compression round index
   cleared : whether the circuit is cleared
*)
Instance sha256_invariant
  : invariant_for sha256 (list byte * bool * nat * nat * bool) :=
  fun (state : denote_type ((Bit ** sha_block ** sha_digest ** BitVec 6 ** Bit)
                            ** state_of sha256_padder
                            ** state_of sha256_inner))
    repr =>
    let '((ready, (block, (digest, (count, done)))),
          (sha256_padder_state, sha256_inner_state)) := state in
    let '(msg, msg_complete, byte_index, t, cleared) := repr in
    (* block index is byte_index / 64 (64 bytes per block) *)
    let block_index := byte_index / 64 in
    (* the message according to sha256_inner is the padded message up to the
       latest block that has been passed to it *)
    let inner_msg := firstn (block_index * 16) (SHA256.padded_msg msg) in
    (* sha256_inner is cleared if either the whole circuit is cleared, or we
       just started a new message and the padder hasn't finished the first block
       yet *)
    let inner_cleared := if cleared
                         then true
                         else byte_index <? 64 in
    (* sha256_inner is done if it's cleared or t = 64 *)
    let inner_done := if inner_cleared then true else t =? 64 in
    (* padder is done if the current byte index is at the end of the message *)
    let padder_done := if cleared
                       then true
                       else if msg_complete
                            then byte_index =? padded_message_size msg
                            else false in
    (* t is within its expected range [0,64) *)
    t < 64
    (* ...and byte index is within its expected range [0,padded_message_size msg] *)
    /\ byte_index <= padded_message_size msg
    (* ...and byte index is always 0 mod 4 *)
    /\ byte_index mod 4 = 0
    (* ...and count is within its expected range [0,17] *)
    /\ (count <= 17)%N
    (* ready is true when count < 16 *)
    /\ ready = (count <? 16)%N
    (* ...and if we're not cleared, the digest must be the expected digest
       (digest is only stored at the end of each inner loop, so can be computed
       for t=0) *)
    /\ (digest = fold_left (SHA256.sha256_step msg)
                          (seq 0 block_index) SHA256.H0)
    (* ...and if we're cleared, we must be in the reset state *)
    /\ (if cleared
       then byte_index = 0
            /\ t = 0
            /\ msg = []
            /\ msg_complete = false
            /\ count = 0%N
            /\ done = true
            /\ digest = SHA256.H0
            /\ block = repeat 0%N 16
       else byte_index <> 0)
    (* ...and if t is nonzero, then the padder must be at a block boundary *)
    /\ (if t =? 0
       then
         if cleared
         then True
         else
           (* padder is still working on this block *)
           byte_index mod 64 <> 0
       else
         byte_index mod 64 = 0
         /\ (if t =? 64
            then count = 0%N
            else count = 17%N))
    (* ...and the index must agree with our state flags *)
    /\ (if done
       then if cleared
            then True
            else byte_index = padded_message_size msg (* index must be at end of message *)
       else
         (* either we're not on the last block, or inner is still working (t < 64) *)
         if t =? 64
         then byte_index < padded_message_size msg
         else True)
    (* ...and the block must be the first [count] words of the ith block of
       the padded message, or 16 if count=17 (unless the circuit is cleared) *)
    /\ (if cleared
       then True
       else if (count =? 17)%N
            then
              block = List.slice 0%N (SHA256.padded_msg msg) block_index 16
              /\ byte_index mod 64 = 0 (* byte index is at the end of a block *)
            else
              skipn (16 - N.to_nat count) block
              = List.slice 0%N (SHA256.padded_msg msg) block_index (N.to_nat count)
              /\ byte_index mod 64 = N.to_nat count * 4 (* byte_index is on the [count]th word *)
              /\ t = 0 (* inner is between blocks *))
    (* ...and the invariant for sha256_padder is satisfied *)
    /\ sha256_padder_invariant
        sha256_padder_state (msg, msg_complete, padder_done, byte_index)
    (* ...and the invariant for sha256_inner is satisfied *)
    /\ sha256_inner_invariant
        sha256_inner_state (inner_msg, block_index, t, inner_done, inner_cleared).

Instance sha256_specification
  : specification_for sha256 (list byte * bool * nat * nat * bool) :=
  {| reset_repr := ([], false, 0, 0, true);
     update_repr :=
       fun (input : denote_type [Bit; sha_word; Bit; BitVec 4; Bit])
         repr =>
         let '(fifo_data_valid,
               (fifo_data, (is_final, (final_length, (clear, _))))) := input in
         let '(msg, msg_complete, byte_index, t, cleared) := repr in
         (* padder is done iff the current byte index is at the end of the
            message *)
         let padder_done := if msg_complete
                            then (byte_index =? padded_message_size msg)
                            else false in
         let new_bytes :=
             new_msg_bytes fifo_data_valid fifo_data is_final final_length in
         if clear
         then ([], false, 0, 0, true)
         else if cleared
              then if fifo_data_valid
                   then (new_bytes, is_final, 4, 0, false)
                   else ([], false, 0, 0, true) (* stay in cleared state *)
              else if byte_index mod 64 =? 0
                   then
                     (* block padding is complete; see if sha256_inner is done
                        by checking if t=64 *)
                     if t =? 64
                     then
                       (* sha256_inner loop is done; start the next block if
                          the padder can proceed, otherwise wait *)
                       if msg_complete
                       then
                         (* step padder, setting t=0 *)
                         (msg, true, byte_index + 4, 0, false)
                       else if fifo_data_valid
                            then
                              (* step padder, setting t=0 *)
                              (msg, true, byte_index + 4, 0, false)
                            else
                              (* message is incomplete and next word isn't
                                 available; hold state and wait *)
                              (msg, msg_complete, byte_index, t, cleared)
                     else
                       (* step sha256_inner loop *)
                       (msg, msg_complete, byte_index, S t, false)
                   else
                     (* block padding is not complete; step padder if we can *)
                     if msg_complete
                     then
                       (* step padder *)
                       (msg, true, byte_index + 4, t, false)
                     else if fifo_data_valid
                          then
                            (* step padder *)
                            (msg, true, byte_index + 4, t, false)
                            else
                              (* message is incomplete and next word isn't
                                 available; hold state and wait *)
                              (msg, msg_complete, byte_index, t, cleared);
     precondition :=
       fun (input : denote_type [Bit; sha_word; Bit; BitVec 4; Bit])
         repr =>
         let '(fifo_data_valid,
               (fifo_data, (is_final, (final_length, (clear, _))))) := input in
         let '(msg, msg_complete, byte_index, t, cleared) := repr in
         let new_bytes :=
             new_msg_bytes fifo_data_valid fifo_data is_final final_length in
         (* the total message length (including any new data) cannot exceed 2 ^
            64 bits (2^61 bytes) -- using N so Coq doesn't try to compute 2 ^ 61
            in nat *)
         (N.of_nat (length (msg ++ new_bytes)) < 2 ^ 61)%N
         (* ..and only pass valid data if circuit is cleared or inner is done
            (i.e. the output "ready" signal is true) *)
         /\ (if fifo_data_valid then if cleared then True else t = 64 else True)
         (* ...and if data is valid, it must be in expected range *)
         /\ (if fifo_data_valid
            then if is_final
                 then (fifo_data < 2 ^ (8 * final_length))%N
                      /\ (1 <= final_length <= 4)%N
                 else (fifo_data < 2 ^ 32)%N
            else True)
         (* ...and if msg_complete is true, then new valid data cannot be passed
            (must clear first) *)
         /\ (if msg_complete then fifo_data_valid = false else True);
     postcondition :=
       fun (input : denote_type [Bit; sha_word; Bit; BitVec 4; Bit])
         repr (output : denote_type (Bit ** sha_digest ** Bit)) =>
         let '(fifo_data_valid,
               (fifo_data, (is_final, (final_length, (clear, _))))) := input in
         let '(msg, msg_complete, byte_index, t, cleared) := repr in
         (* new value of [cleared] *)
         let is_cleared := if clear
                           then true
                           else if cleared
                                then negb (fifo_data_valid)
                                else false in
         let is_cleared_or_done :=
             if is_cleared
             then true
             else if fifo_data_valid
                  then false
                  else if byte_index =? padded_message_size msg
                       then 63 <=? t else false in
         (* new value of [byte_index] *)
         let new_byte_index :=
             if is_cleared
             then 0
             else if byte_index mod 64 =? 0
                  then if t =? 64
                       then if msg_complete
                            then byte_index + 4
                            else if fifo_data_valid
                                 then byte_index + 4
                                 else byte_index
                       else byte_index
                  else if msg_complete
                       then byte_index + 4
                       else if fifo_data_valid
                            then byte_index + 4
                            else byte_index in
         (* new value of [t] *)
         let new_t :=
             if is_cleared
             then 0
             else if byte_index mod 64 =? 0
                  then if t =? 64
                       then if msg_complete
                            then 0
                            else if fifo_data_valid
                                 then 0
                                 else t
                       else S t
                  else t in
         let is_ready :=
             if cleared
             then true
             else if new_byte_index mod 64 =? 0
                  then new_t =? 64 (* ready iff inner is done *)
                  else true in
         exists digest,
           output = (is_cleared_or_done, (digest, is_ready))
           /\ if is_cleared
             then digest = SHA256.H0
             else if is_cleared_or_done
                  then digest = BigEndianBytes.bytes_to_Ns
                                  4 (SHA256.sha256 msg)
                  else True (* no guarantees about intermediate output *)
  |}.

Lemma sha256_invariant_at_reset : invariant_at_reset sha256.
Proof.
  simplify_invariant sha256.
  cbn [reset_state sha256 reset_repr sha256_specification];
    stepsimpl. cbn [Nat.eqb]. compute_expr (0 mod 64).
  ssplit;
    lazymatch goal with
    | |- sha256_padder_invariant _ _ => apply sha256_padder_invariant_at_reset
    | |- sha256_inner_invariant _ _ => apply sha256_inner_invariant_at_reset
    | _ => reflexivity || lia
    end.
Qed.

Lemma sha256_invariant_preserved : invariant_preserved sha256.
Proof.
  simplify_invariant sha256. cbn [absorb_any].
  simplify_spec sha256.
  (* The following gymnastics results in input_, state_, and repr_ being posed
     as let-hypotheses, which makes proof debugging easier because one can look
     at them and see what case the proof is dealing with *)
  intros input state repr.
  pose (input_:=input). pose (state_:=state). pose (repr_:=repr).
  revert dependent repr. revert dependent state. revert dependent input.
  intros (fifo_data_valid,
          (fifo_data, (is_final, (final_length, (clear, []))))).
  intro.
  intros ((ready, (block, (digest, (count, done)))),
          (sha256_padder_state, sha256_inner_state)).
  intro.
  intros ((((msg, msg_complete), byte_index), t), cleared).
  intros; logical_simplify; subst.
  cbv [sha256]; stepsimpl.
  repeat (destruct_inner_pair_let; cbn [fst snd]).
  autorewrite with tuple_if; cbn [fst snd].
  pose proof min_padded_message_size msg.
  pose proof min_padded_message_size
       (new_msg_bytes true fifo_data true final_length).
  pose proof min_padded_message_size
       (msg ++ new_msg_bytes true fifo_data true final_length).
  pose proof padded_message_size_modulo msg.
  pose proof padded_message_size_modulo
       (new_msg_bytes true fifo_data true final_length).
  pose proof padded_message_size_modulo
       (msg ++ new_msg_bytes true fifo_data true final_length).
  ssplit.
  11:
    {
    (* prove that padder invariant is preserved *)
    eapply invariant_preserved_pf; [ | eassumption | ].
    { (* prove that padder state rep is updated correctly *)
      simplify_spec sha256_padder.
      destr clear; [ reflexivity | ].
      destr cleared; logical_simplify; subst.
      { (* cleared=true *)
        destr fifo_data_valid; logical_simplify; subst;
          [ | destruct_one_match; reflexivity ].
        repeat (destruct_one_match; try lia); try reflexivity; [ ].
        lazymatch goal with
        | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
        end.
        reflexivity. }
      { (* cleared=false *)
        destr fifo_data_valid; logical_simplify; subst.
        { (* data_valid=true *)
          destr msg_complete; logical_simplify; subst;
            [ discriminate | ].
          destr (count =? 17)%N; logical_simplify; subst; [ | lia ].
          repeat (destruct_one_match; try lia). }
        { (* data_valid=false *)
          destr msg_complete; logical_simplify; subst;
          rewrite ?Tauto.if_same; [ | reflexivity ].
          assert (byte_index mod 64 = 0 ->
                  byte_index + 4 <> padded_message_size msg) by prove_by_zify.
          repeat (destruct_one_match; try lia).
          all:try reflexivity.
          all:destr (count =? 17)%N; logical_simplify; subst; try lia.
          all:cbn [Nat.eqb] in *; logical_simplify; subst; try lia.
          all:prove_by_zify. } } }
    { (* prove that padder precondition is satisfied *)
      simplify_spec sha256_padder.
      destr fifo_data_valid; logical_simplify; subst; [ | tauto ].
      destr msg_complete; logical_simplify; subst; [ discriminate | ].
      destr is_final; logical_simplify; subst; tauto. } }
  11:
    {
    (* prove that inner invariant is preserved *)
    eapply invariant_preserved_pf; [ | eassumption | ].
    { (* prove that inner state rep is updated correctly *)
      simplify_spec sha256_inner.
      destr clear; [ reflexivity | ].
      destr cleared; logical_simplify; subst;
        [ destr fifo_data_valid; logical_simplify; subst; reflexivity | ].
      destr (byte_index mod 64 =? 0); logical_simplify; subst.
      2:{
        (* not at a block boundary; padder is running *)
        pose proof (Nat.mod_bound_pos byte_index 64 ltac:(lia) ltac:(lia)).
        destr msg_complete; logical_simplify; subst.
        { repeat destruct_one_match; subst; try lia.
          all:cbn [N.eqb Pos.eqb] in *.
          all:logical_simplify; subst.
          all:cbn [Nat.eqb] in *.
          all:logical_simplify; subst.
          all:try lia.
          all:rewrite ?Nat.div_small by lia.
          all:cbn [Nat.mul]; push_firstn; listsimpl.
          all:repeat lazymatch goal with
                     | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                     | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); subst; try lia
                     end.
          all:try reflexivity.
      { (* at block boundary; inner is running *)
        destr (t =? 64); subst; cbn [Nat.eqb] in *; logical_simplify; subst.
        { 
      
        cbn.
        cbn [Nat.eqb] in *.
        change (0 / 64) with 0. cbn [N.eqb Pos.eqb Nat.mul Nat.add].
        repeat (destruct_one_match; try lia); try reflexivity; [ ].
        lazymatch goal with
        | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
        end.
        reflexivity. }
      { (* cleared=false *)
        destr fifo_data_valid; logical_simplify; subst.
        { (* data_valid=true *)
          destr msg_complete; logical_simplify; subst;
            [ discriminate | ].
          destr (count =? 17)%N; logical_simplify; subst; [ | lia ].
          repeat (destruct_one_match; try lia). }
        { (* data_valid=false *)
          destr msg_complete; logical_simplify; subst;
          rewrite ?Tauto.if_same; [ | reflexivity ].
          assert (byte_index mod 64 = 0 ->
                  byte_index + 4 <> padded_message_size msg) by prove_by_zify.
          repeat (destruct_one_match; try lia).
          all:try reflexivity.
          all:destr (count =? 17)%N; logical_simplify; subst; try lia.
          all:cbn [Nat.eqb] in *; logical_simplify; subst; try lia.
          all:prove_by_zify. } } }
    { (* prove that padder precondition is satisfied *)
      simplify_spec sha256_padder.
      destr fifo_data_valid; logical_simplify; subst; [ | tauto ].
      destr msg_complete; logical_simplify; subst; [ discriminate | ].
      destr is_final; logical_simplify; subst; tauto. } }
      





        
  destruct clear; logical_simplify; subst.
  { (* clear=true case *)
    ssplit; try reflexivity; try lia; [ | ].
    { (* prove that padder precondition is satisfied *)
      eapply invariant_preserved_pf; [ | eassumption | ];
        [ reflexivity | ].
      simplify_spec sha256_padder.
      destruct msg_complete; repeat destruct_one_match;
        try discriminate; ssplit; lia. }
    { (* prove that inner precondition is satisfied *)
      eapply invariant_preserved_pf; [ | eassumption | ];
        [ reflexivity | ].
      simplify_spec sha256_inner.
      pose proof Nat.mod_bound_pos byte_index 64 ltac:(lia) ltac:(lia).
      repeat destruct_one_match; logical_simplify; subst.
      all:cbn [N.eqb Pos.eqb] in *; logical_simplify; subst.
      all:change (0 / 64) with 0.
      all:pull_snoc; natsimpl; cbn [fold_left seq].
      all:ssplit; try reflexivity; try lia.
      (* should only be one goal left now *)
      eapply fold_left_ext_In; intros *.
      rewrite in_seq; intros.
      rewrite sha256_step_alt_firstn by lia.
      rewrite sha256_step_alt_equiv; reflexivity. } }
Qed.
