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
         exists out_valid out_value out_done,
           output = (out_valid, (out_value, out_done))
           /\ (if consumer_ready
              then
                out_valid =
                 (if clear
                  then false
                  else if padder_done
                       then data_valid (* valid only if we got new valid data *)
                       else if msg_complete
                            then true (* message is done, produce valid output always *)
                            else data_valid (* we're partway through processing message *))
                /\ out_done =
                  (if clear
                   then true
                   else if padder_done
                        then negb data_valid
                        else if msg_complete
                             then index + 4 =? padded_message_size msg
                             else false)
                /\ (if out_valid
                   then out_value = nth word_index expected_words 0%N
                   else True)
              else True (* no guarantees about output if consumer isn't ready *))
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

(* NOTE: To show CI progress *)
Print Debug GC.
Optimize Heap.
Print Debug GC.

Check expected_padder_state_cases.


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

(* NOTE: To show CI progress *)
Check sha256_padder_invariant_preserved.

Local Ltac testbit_crush :=
  repeat lazymatch goal with
         | |- context [N.eqb ?x ?y] => destr (N.eqb x y); try lia; subst
         | |- N.testbit ?x _ = N.testbit ?x _ => f_equal; lia
         | H: (?X < ?Y)%N |- context [if (?X <? ?Y)%N then _ else _] =>
           rewrite (proj2 (N.ltb_lt X Y) H)
         | _ => first [ progress (push_Ntestbit; boolsimpl) | reflexivity ]
         end.
Local Ltac destruct_padder_state_cases :=
  let padder_state_cases := fresh in
  lazymatch goal with
  | H : context [expected_padder_state ?msg ?mc ?pd ?i] |- _ =>
    pose proof
         expected_padder_state_cases msg mc pd i
         ltac:(lia) ltac:(eauto) ltac:(repeat destruct_one_match;lia)
      as padder_state_cases
  end;
  let H := fresh in
  destruct padder_state_cases as [H|[H|[H|H]]];
  logical_simplify; subst;
  lazymatch goal with H : expected_padder_state _ _ _ _ = _ |- _ =>
                      rewrite H in * end;
  padder_state_simpl.

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
      do 3 eexists; ssplit; (lia || reflexivity) | ].
  destruct consumer_ready;
    repeat (boolsimpl || subst || logical_simplify);
    rewrite ?N.eqb_refl;
    (* handle case for consumer_ready=false *)
    [ | do 3 eexists; ssplit; (lia || reflexivity) ].

  (* useful assertions *)
  pose proof padded_message_bytes_longer_than_input msg.
  pose proof min_padded_message_size msg.
  pose proof padded_message_size_modulo msg.
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

  do 3 eexists; ssplit; [ reflexivity | | | ].
  { (* prove output_valid matches spec *)
    repeat destruct_one_match; destr data_valid; logical_simplify; subst;
      rewrite ?N.eqb_refl; boolsimpl; try reflexivity;
        destruct_padder_state_cases; try discriminate; reflexivity. }
  { (* prove done flag matches spec *)
    destr padder_done; logical_simplify; subst; boolsimpl; [ reflexivity | ].
    destruct_padder_state_cases; boolsimpl.
    all:repeat lazymatch goal with
               | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
               end.
    all:repeat destruct_one_match; logical_simplify; subst.
    all:try lia; try reflexivity.
    all:rewrite ?N.eqb_refl; boolsimpl; try reflexivity.
    all:destr data_valid; logical_simplify; subst; boolsimpl.
    all:try lia.
    all:prove_by_zify. }

  (* remaining case: prove output value matches spec *)
  destruct data_valid;
    repeat (boolsimpl || subst || logical_simplify);
    padder_state_simpl.
  { (* data_valid=true *)
    destruct_padder_state_cases;
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
    destruct padder_done;
      logical_simplify; subst; rewrite ?N.eqb_refl;
        padder_state_simpl; boolsimpl;
          (* solve padder_done=true case *)
          [ eexists; split; reflexivity | ].
    destruct_padder_state_cases.
    { (* state=padder_waiting *)
      tauto. }
    { (* state=padder_emit_bit *)
      rewrite nth_padded_msg. natsimpl. rewrite Nat.mul_div_exact_r by lia.
      cbv [SHA256.padded_msg_bytes]. push_nth. natsimpl. listsimpl.
      rewrite !app_nth1 by (push_length; prove_by_zify).
      natsimpl. push_nth. reflexivity. }
    { (* state=padder_flushing *)
      rewrite nth_padded_msg. natsimpl. rewrite Nat.mul_div_exact_r by lia.
      cbv [SHA256.padded_msg_bytes]. push_nth. natsimpl. listsimpl.
      rewrite !app_nth1 by (push_length; prove_by_zify).
      rewrite !nth_padding_nonzero by lia.
      reflexivity. }
    { (* state=writing_length *)
      push_length.
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

(* NOTE: To show CI progress *)
Check sha256_padder_output_correct.

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
  : invariant_for sha256 (list byte * bool * nat * nat * nat * bool) :=
  fun (state : denote_type ((Bit ** sha_block ** sha_digest ** BitVec 6 ** Bit)
                            ** state_of sha256_padder
                            ** state_of sha256_inner))
    repr =>
    let '((ready, (block, (digest, (count, done)))),
          (sha256_padder_state, sha256_inner_state)) := state in
    let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := repr in
    (* block index is byte_index / 64 (64 bytes per block) *)
    let padder_block_index := padder_byte_index / 64 in
    let inner_block_index := inner_byte_index / 64 - 1 in
    (* compute representation for padder state *)
    let padder_repr :=
        if cleared
        then (reset_repr (c:=sha256_padder))
        else (msg, msg_complete,
              padder_byte_index =? padded_message_size msg, padder_byte_index) in
    (* compute representation for inner *)
    let inner_repr :=
        if cleared
        then (reset_repr (c:=sha256_inner))
        else
          (firstn (inner_byte_index / 64 * 16) (SHA256.padded_msg msg)
           , inner_block_index
           , t
           , if t =? 64 then true else inner_byte_index =? 0
           , inner_byte_index =? 0) in
    (* index of the block that's currently in progress (i.e. next block whose
       digest will be produced) *)
    let completed_block_index :=
        if (count <=? 15)%N
        then
          (* padder is running; same block index the padder is on *)
          padder_block_index
        else if (count =? 16)%N
             then
               (* padder is done, so padder_block_index has just moved to the
                  next block; subtract 1 to get the current index *)
               padder_block_index - 1
             else
               if t =? 64
               then
                 (* inner circuit is done; next block to be produced will be
                    whatever block index the padder is on *)
                 padder_block_index
               else
                 (* inner circuit is in progress; next block to be produced will
                    be whatever block index the inner circuit is on *)
                 inner_block_index in
    (* the invariant for sha256_padder is satisfied *)
    sha256_padder_invariant sha256_padder_state padder_repr
    (* ...and the invariant for sha256_inner is satisfied *)
    /\ sha256_inner_invariant sha256_inner_state inner_repr
    (* ...and the length of [block] is always 16 *)
    /\ length block = 16
    (* ...and count is always in the range [0,17] *)
    /\ (count <= 17)%N
    (* ...and byte indices are always at a word boundary *)
    /\ padder_byte_index mod 4 = 0
    /\ (if cleared
       then
         (* if the circuit is cleared, it must be in the reset state
            (including subcircuits) *)
         padder_byte_index = 0
         /\ inner_byte_index = 0
         /\ t = 0
         /\ msg = []
         /\ msg_complete = false
         /\ count = 0%N
         /\ done = true
         /\ digest = SHA256.H0
       else
         (* the byte index (padder counter) is within the range
            [4,padded_message_size msg] *)
         4 <= padder_byte_index <= padded_message_size msg
         (* ...and t (inner loop counter) is in the range [0,64] *)
         /\ t <= 64
         (* ...and ready is true iff count < 16 *)
         /\ ready = (count <? 16)%N
         (* ...and the digest must be the expected digest (digest is only
            stored at the end of each inner loop) *)
         /\ digest = fold_left (SHA256.sha256_step msg)
                              (seq 0 completed_block_index) SHA256.H0
         (* ...and the index is past the end of the message iff the message is
            complete *)
         /\ (if msg_complete then length msg <= padder_byte_index else padder_byte_index = length msg)
         (* ...and if [done] is true, we must be at the end of the message *)
         /\ (if done
            then padder_byte_index = inner_byte_index
                 /\ padder_byte_index = padded_message_size msg
                 /\ count = 0%N
                 /\ t = 64
            else True)
         (* ...and the state variables agree with [count] *)
         /\ (if (count <=? 15)%N
            then
              (* padder is running *)
              skipn (16 - N.to_nat count) block
              = List.slice 0%N (SHA256.padded_msg msg) (padder_block_index * 16) (N.to_nat count)
              /\ padder_byte_index mod 64 = N.to_nat count * 4 (* byte_index is on the [count]th word *)
              /\ (if (padder_byte_index <? 64) then t = 0 else t = 64) (* inner is between blocks *)
              /\ inner_byte_index = padder_block_index * 64
            else
              (* inner loop is running or about to run *)
              padder_byte_index mod 64 = 0 (* byte index is at the end of a block *)
              /\ (if (count =? 16)%N
                 then
                   (* padder has just finished a block; send the completed
                        block to start inner loop *)
                   block = List.slice 0%N (SHA256.padded_msg msg)
                                      (inner_byte_index / 64 * 16) 16
                   /\ (if (padder_byte_index =? 64) then t = 0 else t = 64)
                   /\ padder_byte_index = inner_byte_index + 64
                 else
                   (* inner loop is in progress *)
                   0 <= t < 64
                   /\ inner_byte_index = padder_byte_index))
      ).

Instance sha256_specification
  : specification_for sha256 (list byte * bool * nat * nat * nat * bool) :=
  {| reset_repr := ([], false, 0, 0, 0, true);
     update_repr :=
       fun (input : denote_type [Bit; sha_word; Bit; BitVec 4; Bit])
         repr =>
         let '(fifo_data_valid,
               (fifo_data, (is_final, (final_length, (clear, _))))) := input in
         let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := repr in
         let new_bytes :=
             new_msg_bytes fifo_data_valid fifo_data is_final final_length in
         if clear
         then ([], false, 0, 0, 0, true)
         else if cleared
              then if fifo_data_valid
                   then (new_bytes, is_final, 4, 0, 0, false)
                   else ([], false, 0, 0, 0, true) (* stay in cleared state *)
              else if (padder_byte_index =? inner_byte_index)
                   then if t =? 64
                        then
                          (* sha256_inner has finished; start the padder on the
                             next block if we can *)
                          if (padder_byte_index =? padded_message_size msg)
                          then
                            (* padder is at the end of the message and
                               processing is completely done; hold state
                               constant *)
                            repr
                          else
                            if msg_complete
                            then
                              (* step padder *)
                              (msg, msg_complete, padder_byte_index + 4, inner_byte_index, t, cleared)
                            else if fifo_data_valid
                                 then
                                   (* step padder *)
                                   (msg ++ new_bytes, is_final, padder_byte_index + 4, inner_byte_index, t, cleared)
                                 else
                                   (* message is incomplete and next word isn't
                                      available; wait *)
                                   repr
                        else
                          (* sha256_inner is already in progress; increment t *)
                          (msg, msg_complete, padder_byte_index, inner_byte_index, S t, cleared)
                   else
                     if (padder_byte_index =? inner_byte_index + 64)
                     then
                       (* padder just finished a block; start sha256_inner by
                          passing in the new block and reset t to 0 *)
                       (msg, msg_complete, padder_byte_index, padder_byte_index, 0, cleared)
                     else
                       (* padder is midway through a block; take another step if possible *)
                       if msg_complete
                       then
                         (* step padder *)
                         (msg, msg_complete, padder_byte_index + 4, inner_byte_index, t, cleared)
                       else if fifo_data_valid
                            then
                              (* step padder *)
                              (msg ++ new_bytes, is_final, padder_byte_index + 4, inner_byte_index, t, cleared)
                            else
                              (* message is incomplete and next word isn't
                                 available; wait *)
                              (msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared);
     precondition :=
       fun (input : denote_type [Bit; sha_word; Bit; BitVec 4; Bit])
         repr =>
         let '(fifo_data_valid,
               (fifo_data, (is_final, (final_length, (clear, _))))) := input in
         let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := repr in
         let new_bytes :=
             new_msg_bytes fifo_data_valid fifo_data is_final final_length in
         (* the total message length (including any new data) cannot exceed 2 ^
            64 bits (2^61 bytes) -- using N so Coq doesn't try to compute 2 ^ 61
            in nat *)
         (N.of_nat (length (msg ++ new_bytes)) < 2 ^ 61)%N
         (* ..and only pass valid data if circuit is cleared or inner is done
            (i.e. the output "ready" signal is true) *)
         /\ (if fifo_data_valid
            then if cleared
                 then True
                 else t = 64 /\ msg_complete = false
            else True)
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
         let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := repr in
         (* new value of [cleared] *)
         let is_cleared := if clear
                           then true
                           else if cleared
                                then negb (fifo_data_valid)
                                else false in

         let count_16_pre :=
             if (if (padder_byte_index =? 64) then t =? 0 else t =? 64)
             then if (padder_byte_index =? inner_byte_index + 64) then true else false else false
         in
         let count_le15_pre :=
             if (padder_byte_index <? 64) then t =? 0 else t =? 64
         in

         let is_cleared_or_done :=
             if is_cleared
             then true
             else if fifo_data_valid
                  then false
                  else
                    if count_16_pre
                    then false
                    else
                     if (padder_byte_index =? padded_message_size msg) then if (t =? 64) then true else false else false
         in

         (* new value of [padder_byte_index] *)
         let new_padder_byte_index :=
             if clear
             then 0
             else if cleared
              then 0
              else if (padder_byte_index =? inner_byte_index)
                   then if t =? 64
                        then if (padder_byte_index =? padded_message_size msg)
                             then padder_byte_index
                             else if msg_complete
                                  then padder_byte_index + 4
                                  else if fifo_data_valid
                                       then padder_byte_index + 4
                                       else padder_byte_index
                        else padder_byte_index
                   else if (padder_byte_index =? inner_byte_index + 64)
                        then padder_byte_index
                        else if msg_complete
                             then padder_byte_index + 4
                             else if fifo_data_valid
                                  then padder_byte_index + 4
                                  else padder_byte_index in

         (* new value of [t] *)
         let new_t :=
             if clear
             then 0
             else if cleared
                  then 0
                  else if (padder_byte_index =? inner_byte_index)
                       then if t =? 64
                            then t
                            else S t
                       else if (padder_byte_index =? inner_byte_index + 64)
                            then 0
                            else t in

         (* ready for new input only if the inner loop is done and the padder is
            not *)
         let is_ready :=
             if is_cleared
             then true
             else
               if count_16_pre then false
               else if count_le15_pre then
                 if (if padder_byte_index =? padded_message_size msg
                   then fifo_data_valid
                   else if msg_complete then true else fifo_data_valid)
                 then padder_byte_index mod 64 <=? 56
                 else true
               else if inner_byte_index =? padder_byte_index
                 then
                   if if (t =? 64)%nat then true else (inner_byte_index =? 0)%nat
                   then true
                   else (t =? 63)%nat
                 else true
         in

         exists done digest ready,
           output = (done, (digest, ready))
           /\ done = is_cleared_or_done
           /\ ready = is_ready
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
  cbn [reset_repr reset_state sha256 sha256_specification
                  sha256_padder_specification
                  sha256_inner_specification].
  stepsimpl. cbn [Nat.eqb]. compute_expr (0 mod 64).
  ssplit;
    lazymatch goal with
    | |- sha256_padder_invariant _ _ => apply sha256_padder_invariant_at_reset
    | |- sha256_inner_invariant _ _ => apply sha256_inner_invariant_at_reset
    | _ => reflexivity || lia
    end.
Qed.

Ltac simplify_postcondition c :=
  let x := constr:((_ : specification_for c _)) in
  match x with
  | ?x => cbn[x postcondition] in *
  end.
(* TODO: move *)
Ltac use_correctness' c :=
  lazymatch goal with
  | |- context [ @snd ?A ?B (@step ?i ?s ?o c ?state ?input) ] =>
    find_correctness c;
    pose proof (@output_correct_pf
                  s i o c _ _ _ _
                  input state _ ltac:(eassumption) ltac:(eassumption));
    generalize dependent (@snd A B (@step i s o c state input)); intros;
    try simplify_postcondition c; logical_simplify; subst
  end.

(* TODO: move *)
Lemma resize_small {A} n d (ls : list A) :
  n <= length ls ->
  List.resize d n ls = firstn n ls.
Proof.
  intros; cbv [List.resize]. natsimpl.
  cbn [repeat]; listsimpl; reflexivity.
Qed.

(* TODO: move *)
Lemma firstn_slice_app {A} n (ls : list A) d len :
  n + len <= length ls ->
  firstn n ls ++ List.slice d ls n len = firstn (n + len) ls.
Proof.
  intros. cbv [List.slice]. rewrite resize_small by length_hammer.
  rewrite <-(firstn_skipn n ls).
  repeat (push_firstn || push_skipn || push_length || natsimpl || listsimpl).
  reflexivity.
Qed.

(* TODO: move *)
Lemma firstn_padded_msg_truncate n msg1 msg2  :
  n * 4 <= length msg1 ->
  firstn n (SHA256.padded_msg (msg1 ++ msg2)) = firstn n (SHA256.padded_msg msg1).
Proof.
  intros. pose proof padded_message_size_mono msg1 msg2.
  pose proof padded_message_bytes_longer_than_input msg1.
  rewrite !firstn_map_nth with (d:=0%N) by (push_length; prove_by_zify).
  eapply map_ext_in. intros *; rewrite in_seq; intros.
  rewrite !nth_padded_msg. cbv [SHA256.padded_msg_bytes].
  rewrite <-!app_assoc. push_nth. reflexivity.
Qed.

Lemma slicen_padded_msg_truncate n msg1 msg2 c d :
  n * 4 + c * 4 <= length msg1 ->
  List.slice d (SHA256.padded_msg (msg1 ++ msg2)) n c = List.slice d (SHA256.padded_msg msg1) n c.
Proof.
  intros. pose proof padded_message_size_mono msg1 msg2.
  pose proof padded_message_bytes_longer_than_input msg1.
  cbv [List.slice List.resize].
  push_length.
  assert (c - (padded_message_size msg1 / 4 - n) = 0) by prove_by_zify.
  assert (c - (padded_message_size (msg1 ++ msg2) / 4 - n) = 0) by prove_by_zify.
  rewrite H2, H3.
  rewrite ?firstn_skipn_comm.
  now rewrite firstn_padded_msg_truncate by lia.
Qed.

(* TODO: move *)
Lemma skipn_tl {A} n (ls : list A) :
  skipn n (tl ls) = skipn (S n) ls.
Proof. induction ls; intros; push_skipn; cbn [tl]; reflexivity. Qed.
Hint Rewrite @skipn_tl : push_skipn.

(* TODO: move *)
Hint Rewrite Nat.mul_0_l Nat.mul_0_r Nat.mul_1_l Nat.mul_1_r : natsimpl.
Hint Rewrite Nat.div_1_r : natsimpl.
Hint Rewrite Nat.mod_1_r : natsimpl.
Ltac natsimpl_step ::= first
  [ progress autorewrite with natsimpl
  | rewrite Min.min_r by lia
  | rewrite Min.min_l by lia
  | rewrite Nat.add_sub by lia
  | rewrite (fun n m => proj2 (Nat.sub_0_le n m)) by lia
  | rewrite Nat.div_0_l by lia
  | rewrite Nat.div_same by lia
  | rewrite Nat.mod_0_l by lia
  | rewrite Nat.mod_same by lia
  | rewrite Nat.mod_1_l by lia
  ].

(* TODO: move to SHA256Properties *)
Lemma fold_left_sha256_step_alt_firstn i H msg :
  fold_left (SHA256.sha256_step msg) (seq 0 i) H =
  fold_left (SHA256Alt.sha256_step (firstn (i * 16) (SHA256.padded_msg msg))) (seq 0 i) H.
Proof.
  intros; eapply fold_left_ext_In; intros *.
  rewrite in_seq; intros.
  rewrite sha256_step_alt_firstn by lia.
  rewrite sha256_step_alt_equiv; reflexivity.
Qed.

Lemma fold_left_sha256_step_alt_firstn' i j H msg :
  j < i ->
  fold_left (SHA256.sha256_step msg) (seq 0 j) H =
  fold_left (SHA256Alt.sha256_step (firstn (i * 16) (SHA256.padded_msg msg))) (seq 0 j) H.
Proof.
  intros; eapply fold_left_ext_In; intros *.
  rewrite in_seq; intros.
  rewrite sha256_step_alt_firstn by lia.
  rewrite sha256_step_alt_equiv; reflexivity.
Qed.

(* TODO: move to SHA256Properties *)
(* M returns the same result regardless of blocks above the current block
   index *)
Lemma sha256_M_truncate msg1 msg2 j i :
  (S i * 64 <= length msg1)%nat -> (j < 16)%nat ->
  SHA256.M (msg1 ++ msg2) j i = SHA256.M msg1 j i.
Proof.
  cbv [SHA256.M]; intros.
  rewrite !nth_padded_msg. apply f_equal.
  cbv [SHA256.padded_msg_bytes].
  rewrite <-!app_assoc; push_nth.
  reflexivity.
Qed.

(* TODO: move to SHA256Properties *)
(* W returns the same result regardless of blocks above the current block
   index *)
Lemma sha256_W_truncate msg1 msg2 i :
  (S i * 64 <= length msg1)%nat -> SHA256.W (msg1 ++ msg2) i = SHA256.W msg1 i.
Proof.
  cbv [SHA256.W]. intros.
  eapply fold_left_ext_In. intros *; rewrite in_seq; natsimpl; intros.
  destruct_one_match; [ | reflexivity ].
  rewrite sha256_M_truncate by lia.
  reflexivity.
Qed.

(* TODO: move to SHA256Properties *)
(* sha256_step returns the same result regardless of blocks above the current index *)
Lemma sha256_step_truncate msg1 msg2 i H :
  (S i * 64 <= length msg1)%nat ->
  SHA256.sha256_step (msg1 ++ msg2) H i = SHA256.sha256_step msg1 H i.
Proof.
  cbv [SHA256.sha256_step]. intros. apply f_equal2; [ reflexivity | ].
  apply fold_left_ext_In; intros *. rewrite in_seq; natsimpl; intros.
  rewrite sha256_W_truncate by lia. reflexivity.
Qed.

Lemma length_concat' {A} (x: list (list A)) n: n + length (concat x) = fold_left (fun acc x => acc + length x) x n.
Proof.
  revert n.
  induction x; [now cbn |].
  intro n.
  rewrite concat_cons.
  rewrite fold_left_cons.
  push_length.
  rewrite Nat.add_assoc.
  apply IHx.
Qed.

Lemma length_concat {A} (x: list (list A)): length (concat x) = fold_left (fun acc x => acc + length x) x 0.
Proof.
  rewrite <- Nat.add_0_l at 1.
  apply length_concat'.
Qed.

Lemma test_nth_byte_of_x x i :
  (x < 2 ^ 32)%N ->
  N.testbit
  (Byte.to_N
     (nth (N.to_nat (i / 8))
        [N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 3) * 8));
        N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 2) * 8));
        N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 1) * 8));
        N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 0) * 8))] "000"%byte))
  (i mod 8) = N.testbit x i.
Proof.
  intros.
  remember (N.to_nat (i/8)) as m.
  destr (m <? 4).
  {
  repeat (destruct m as [m|]; try prove_by_zify);
    cbn [List.app nth Nat.mul Nat.add];
    rewrite N2Byte.id;
    replace 256%N with (2^8)%N by now cbn.
  { assert(i < 8)%N by prove_by_zify.
    rewrite N.mod_small with (b:=8%N) by lia.
    testbit_crush.
  }
  { assert(i - 8 < 8)%N by prove_by_zify.
    replace (i mod 8)%N with ((i - 8) mod 8)%N by prove_by_zify.
    rewrite N.mod_small with (b:=8%N) by lia.
    cbn [Nat.sub].
    testbit_crush.
    now replace ((i - 8 + N.of_nat 1 * 8))%N with i by prove_by_zify.
  }
  { assert(i - 16 < 8)%N by prove_by_zify.
    replace (i mod 8)%N with ((i - 16) mod 8)%N by prove_by_zify.
    rewrite N.mod_small with (b:=8%N) by lia.
    cbn [Nat.sub].
    testbit_crush.
    now replace ((i - 16 + N.of_nat 2 * 8))%N with i by prove_by_zify.
  }
  { assert(i - 24 < 8)%N by prove_by_zify.
    replace (i mod 8)%N with ((i - 24) mod 8)%N by prove_by_zify.
    rewrite N.mod_small with (b:=8%N) by lia.
    cbn [Nat.sub].
    testbit_crush.
    now replace ((i - 24 + N.of_nat 3 * 8))%N with i by prove_by_zify.
  }
  }
  assert (32 <= i)%N by prove_by_zify.
  rewrite nth_overflow by now push_length.
  destr (x=?0)%N;subst;push_Ntestbit;[reflexivity|].
  apply N.log2_lt_pow2 in H.
  { rewrite N.bits_above_log2; lia. }
  lia.
Qed.


Lemma concat_digest_to_N_id xs:
  Forall (fun x => x < 2 ^ 32)%N xs ->
  length xs = 8 ->
  BigEndianBytes.bytes_to_Ns 4 (SHA256.concat_digest xs) = xs.
Proof.
  intros.
  cbv [SHA256.concat_digest SHA256.w].
  cbv [seq SHA256.w].
  replace (N.to_nat 32 / 8) with 4 by prove_by_zify.

  repeat (destruct xs as [ | ?x xs];[now cbn in *| cbn in H0;
    let h := fresh in pose proof (Forall_inv H) as h;
    cbn beta in h;
    let h' := fresh in
    pose proof (Forall_inv_tail H) as h';
    clear H; rename h' into H;
    try lia]).
  clear H.
  destruct xs;[|cbn in H0; lia].

  apply nth_ext with (d:=0%N) (d':=0%N).
  { now cbn. }
  intros.
  cbv [SHA256.concat_digest].
  rewrite nth_bytes_to_Ns; cycle 1.
  { now cbn.  }
  { lia. }

  revert H.
  rewrite flat_map_concat_map.
  cbv [seq].
  cbn [List.map seq nth Nat.mul Nat.add concat List.app].
  cbv [BigEndianBytes.N_to_bytes seq BigEndianBytes.bytes_to_Ns ].
  push_length; intros.
  cbv [List.map].
  repeat (destruct n; [
    cbn [List.app nth Nat.mul Nat.add];
    apply N.bits_inj; intro i;
    rewrite concat_bytes_spec;
    apply test_nth_byte_of_x; trivial
  |]).
  exfalso; prove_by_zify.
Qed.

(* NOTE: To show CI progress *)
Print Debug GC.
Check concat_digest_to_N_id.

Require Import Coq.derive.Derive.

(* simplifies the sha256 circuit so we don't have to wait for the slow
   simplifications in every proof *)
Derive step_sha256_simplified
       SuchThat
       (forall ready block digest count done sha256_padder_state sha256_inner_state
          fifo_data_valid fifo_data is_final final_length clear,
           let state := ((ready, (block, (digest, (count, done)))),
                         (sha256_padder_state, sha256_inner_state)) in
           let input := (fifo_data_valid,
                         (fifo_data, (is_final, (final_length, (clear, tt))))) in
           step sha256 state input =
           step_sha256_simplified ready block digest count done sha256_padder_state sha256_inner_state
                                  fifo_data_valid fifo_data is_final final_length clear)
       As step_sha256_simplified_eq.
Proof.
  cbv [sha256]; intros; stepsimpl.
  repeat (destruct_inner_pair_let; cbn [fst snd]).
  rewrite <-!tup_if. cbn [fst snd].
  subst step_sha256_simplified. instantiate_app_by_reflexivity.
Qed.

(* NOTE: To show CI progress *)
Check step_sha256_simplified.
Print Debug GC.
Optimize Heap.
Print Debug GC.

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
  intros (((((msg, msg_complete), padder_byte_index), inner_byte_index), t), cleared).
  intros; logical_simplify; subst.

  rewrite step_sha256_simplified_eq. cbv [step_sha256_simplified]. cbn [fst snd].
  rewrite <-!tup_if. cbn [fst snd].

  (* A whole bunch of assertions about the properties of padded_message_size
     related to all 3 possible next messages *)
  pose proof padded_message_size_mono
       msg (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_bytes_longer_than_input msg.
  pose proof padded_message_bytes_longer_than_input
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_bytes_longer_than_input
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof min_padded_message_size msg.
  pose proof min_padded_message_size
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof min_padded_message_size
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_size_modulo msg.
  pose proof padded_message_size_modulo
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_size_modulo
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).

  (* prove that padder precondition is satisfied *)
  lazymatch goal with
  | H : sha256_padder_invariant ?state ?repr
    |- context [step sha256_padder ?state ?input] =>
    assert (precondition sha256_padder input repr)
  end.
  { simplify_spec sha256_padder. cbn [reset_repr sha256_padder_specification].
    destr cleared; logical_simplify; subst;
      [ destr fifo_data_valid; destr is_final; logical_simplify; subst;
        ssplit; solve [auto] | ].
    ssplit; [ assumption | ].
    destr fifo_data_valid; logical_simplify; subst; [ | tauto ].
    destr is_final; logical_simplify; subst; tauto. }

  use_correctness' sha256_padder.
  cbn [reset_repr sha256_padder_specification] in *.

  (* prove that inner precondition is satisfied *)
  lazymatch goal with
  | H : sha256_inner_invariant ?state ?repr
    |- context [step sha256_inner ?state ?input] =>
    assert (precondition sha256_inner input repr)
  end.
  { simplify_spec sha256_inner. cbn [reset_repr sha256_inner_specification].
    destr cleared; logical_simplify; subst;
      [ destr fifo_data_valid; destr is_final; logical_simplify; subst;
        ssplit; solve [auto] | ].
    rewrite fold_left_sha256_step_alt_firstn.
    all:destr (t =? 64); logical_simplify; subst; try lia.
    all:destr (count <=? 15)%N; logical_simplify; subst.
    all:destr (count =? 16)%N; logical_simplify; subst; try lia.
    all:repeat (destruct_one_match; logical_simplify; subst; try lia).
    all:repeat lazymatch goal with
               | H : (Nat.eqb ?x ?y) = false |- _ => apply Nat.eqb_neq in H
               end.
    all:try (destr (padder_byte_index <? 64); logical_simplify; subst; [ | lia ]).
    all:rewrite ?Nat.div_mul, ?Nat.div_small in * by lia.
    all:try reflexivity.
    all:try discriminate.
    all:natsimpl.
    all:repeat lazymatch goal with
               | |- context [(?x + ?y) / ?y] => replace ((x + y) / y) with (x / y + 1) by prove_by_zify
               | |- context [S (?x - 1)] => replace (S (x - 1)) with x by prove_by_zify
               end.
    all:natsimpl.
    all:try (destr (inner_byte_index + 64 =? 64); logical_simplify; subst; lia).
    all:lazymatch goal with
        | |- _ /\ _ /\ _ => ssplit; [ reflexivity | | length_hammer ]
        | _ => idtac
        end.
    all:rewrite ?firstn_slice_app by (push_length; prove_by_zify).
    all:lazymatch goal with
        | |- fold_left _ _ _ = fold_left _ _ _ =>
          eapply fold_left_ext_In; intros *;
            rewrite in_seq; intros;
              rewrite !sha256_step_alt_firstn by lia;
              try reflexivity
        end. }

  use_correctness' sha256_inner.
  cbn [reset_repr sha256_inner_specification] in *.

  Optimize Proof.
  ssplit.
  { (* prove that padder invariant is preserved *)
    eapply invariant_preserved_pf; [ | eassumption .. ].
    (* prove that padder state rep is updated correctly *)
    cbn [reset_repr update_repr sha256_padder_specification] in *.
    destr clear; [ destruct cleared; reflexivity | ].
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
      destr fifo_data_valid; logical_simplify; subst;
      cbn [Nat.eqb].
      { (* data_valid=true *)
        rewrite ?Tauto.if_same.
        destr (length msg =? padded_message_size msg); [ lia | ].
        destr (count <=? 15)%N; logical_simplify; subst;
          [ destr (count =? 0)%N; logical_simplify; subst
          | destr (count =? 16)%N; logical_simplify; subst ].
        all:try lia.
        all:cbn [N.eqb Pos.eqb Nat.eqb] in *.
        all:repeat destruct_one_match; try lia.
        all:repeat lazymatch goal with
                   | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                   end.
        all:try reflexivity.
        all:prove_by_zify. }
      { (* data_valid = false *)
        destr msg_complete; logical_simplify; subst;
        rewrite ?Tauto.if_same; [ | repeat destruct_one_match; reflexivity ].
        assert (padder_byte_index mod 64 = 0 ->
                padder_byte_index + 4 <> padded_message_size msg) by prove_by_zify.
        repeat (destruct_one_match; try lia); logical_simplify; subst.
        all:rewrite ?Nat.eqb_refl; try reflexivity.
        all:repeat lazymatch goal with
                   | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                   end.
        all:destr (count =? 16)%N; subst; try lia.
        all:try (exfalso; prove_by_zify).
        all:destr (padder_byte_index <? 64); lia. } } }

  Optimize Proof.
  { (* prove that inner invariant is preserved *)
    eapply invariant_preserved_pf; [ | eassumption .. ].
    (* prove that inner state rep is updated correctly *)
    cbn [reset_repr update_repr sha256_inner_specification].
    destr clear; [ destr cleared; reflexivity | ].
    destr cleared; logical_simplify; subst;
      [ cbn [N.leb N.compare] in *; logical_simplify; subst;
        destr fifo_data_valid; logical_simplify; subst; reflexivity | ].

    Optimize Proof.
    destr (padder_byte_index =? padded_message_size msg); logical_simplify; subst.
    { (* padder has reached end of message *)
      (* only one possible case for data_valid and msg_complete;
         data_valid=false and msg_complete=true *)
      Eval compute in "At abstract 1"%string.
      abstract(
      destr fifo_data_valid; destr msg_complete;
        logical_simplify; subst; try lia; [ ];
      destr (count <=? 15)%N; logical_simplify; subst;
      rewrite ?Tauto.if_same in *; cbn [fst snd] in *;
      boolsimpl;
      repeat (first [ destruct_one_match | destruct_one_match_hyp];
                  logical_simplify; subst; try lia; try reflexivity);
      try (exfalso; prove_by_zify);
      repeat lazymatch goal with
                 | H : (Nat.eqb ?x ?y) = true |- _ => apply Nat.eqb_eq in H; subst; try lia
                 | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                 | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                 end;
      try reflexivity;
      rewrite firstn_slice_app by (push_length; prove_by_zify);
      (* structure already matches; use prove_by_zify for nat arguments *)
      repeat (f_equal; lazymatch goal with
                           | |- @eq nat _ _ => prove_by_zify
                           | _ => idtac
                         end)). 
    }
    { (* padder is not yet at end of message *)
      destr (padder_byte_index =? inner_byte_index); logical_simplify; subst.
      { (* inner is running or just finished running *)
        destr (t =? 64); logical_simplify; subst.
        { (* inner just finished *)
          rewrite ?Tauto.if_same.
          repeat destruct_one_match; logical_simplify; subst; try lia.
          all:repeat destruct_one_match_hyp; logical_simplify; subst; try lia.
          all:repeat lazymatch goal with
                     | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                     | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                     end.
          all:try reflexivity.
          all:rewrite firstn_padded_msg_truncate by prove_by_zify.
          all:reflexivity. }
        { (* inner is still running *)
          destr fifo_data_valid; logical_simplify; subst; [ lia | ].
          repeat destruct_one_match; logical_simplify; subst; try lia.
          all:rewrite ?N.eqb_refl in *.
          all:repeat (destruct_one_match_hyp; logical_simplify; subst; try lia).
          all:repeat lazymatch goal with
                     | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                     | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                     end.
          all:try reflexivity.
          all:exfalso; prove_by_zify. } }
      { (* padder is running or just finished running *)
        destr (padder_byte_index =? inner_byte_index + 64); logical_simplify; subst.
        { (* padder just finished running (count=16) *)
          destr (count <=? 15)%N; logical_simplify; subst;
            [ exfalso; prove_by_zify | ].
          destr (count =? 16)%N; [ | exfalso; prove_by_zify ].
          subst; rewrite ?N.eqb_refl in *; logical_simplify; subst.
          cbn [Nat.eqb] in *.
          destr (inner_byte_index + 64 =? 64); logical_simplify; subst.
          all:repeat destruct_one_match; logical_simplify; subst; try lia.
          all:repeat lazymatch goal with
                     | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                     | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                     end.
          all:rewrite ?firstn_slice_app by (push_length; prove_by_zify).
          all:rewrite ?Nat.eqb_refl in *; try discriminate.
          (* structure already matches; use prove_by_zify for nat arguments *)
          all:repeat (f_equal; lazymatch goal with
                               | |- @eq nat _ _ => prove_by_zify
                               | _ => idtac
                               end). }
        { (* padder is still running (count <= 15) *)
          destr (count <=? 15)%N; logical_simplify; subst;
          [ | destr (count =? 16)%N; logical_simplify; subst;
              exfalso; prove_by_zify ].
          rewrite ?Tauto.if_same. rewrite ?Nat.eqb_refl.
          destr (padder_byte_index <? 64); logical_simplify; subst; try lia;
            [ rewrite !(Nat.div_small padder_byte_index 64) in * by lia | ].
          all:natsimpl; cbn [Nat.eqb].
          all:repeat destruct_one_match; logical_simplify; subst; try lia.
          all:repeat lazymatch goal with
                     | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                     | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                     end.
          all:try reflexivity.
          all:try prove_by_zify.
          all:rewrite firstn_padded_msg_truncate by prove_by_zify.
          all:reflexivity. } } } }

  Optimize Proof.
  { (* length block = 16 *)
    fold denote_type; change (denote_type sha_word) with N.
    repeat destruct_one_match.
    all:cbn [N.leb Pos.compare N.compare fst snd] in *.
    all:logical_simplify; subst; boolsimpl.
    all:repeat destruct_one_match; length_hammer. }
  { (* count <= 17 *)
    repeat destruct_one_match.
    all:cbn [N.leb Pos.compare N.compare fst snd] in *.
    all:logical_simplify; subst; boolsimpl.
    all:try lia.
    all:boolsimpl_hyps; N.bool_to_prop.
    all:compute_expr (2 ^ N.of_nat 6)%N.
    all:rewrite ?N.mod_small by lia.
    all:lia. }
  { (* padder_byte_index mod 4 = 0 *)
    repeat destruct_one_match; try reflexivity.
    all:try assumption.
    all:prove_by_zify. }

  { (* big if cleared then ... else ... clause *)
    compute_expr (2 ^ N.of_nat 6)%N.
    destr clear; [ ssplit; reflexivity | ].
    destr cleared; logical_simplify; subst.

    { (* cleared=true *)
      cbn [N.leb Pos.compare N.compare fst snd] in *.
      logical_simplify; subst.
      (* if data isn't valid, we stay cleared *)
      destr fifo_data_valid; logical_simplify; subst; boolsimpl;
        [ | ssplit; reflexivity ].
      natsimpl.
      rewrite !Nat.mod_small, !N.mod_small by lia.
      rewrite !Nat.div_small by lia.
      ssplit; try lia.
      all:repeat lazymatch goal with
                 | |- context [N.leb ?x ?y] => destr (N.leb x y); try lia
                 | |- context [N.ltb ?x ?y] => destr (N.ltb x y); try lia
                 end.
      all:try reflexivity.
      all:ssplit; try lia.
      all:repeat destruct_one_match; logical_simplify; subst; try lia.
      all:lazymatch goal with
          | |- context [length (new_msg_bytes _ _ _ _)] => cbv [new_msg_bytes]; length_hammer
          | _ => idtac
          end.
      (* should be only one case left, expression for block *)
      compute_expr (N.to_nat (0 + 1)). natsimpl.
      rewrite skipn_tl.
      (* simplify implicit types *)
      fold denote_type. change (denote_type sha_word) with N.
      push_skipn; listsimpl.
      rewrite slice_map_nth; cbn [List.map seq].
      reflexivity. }
  
    Optimize Proof.

    { (* cleared = false *)
      rewrite ?Tauto.if_same.
      (* destruct cases for [count] *)
      destr (count <=? 15)%N;
        [ destr (count =? 0)%N | destr (count =? 16)%N ];
        logical_simplify; subst; cbn [fst snd] in *.

      { (* count=0 (transition from inner to padder *)
        destr (padder_byte_index =? padder_byte_index / 64 * 64);
          [ | exfalso; prove_by_zify ].
        compute_expr ((0 + 1) mod 64)%N.
        repeat (natsimpl || boolsimpl || cbn [Nat.eqb N.eqb Pos.eqb]).
        ssplit.
        { (* padder_byte_index <= padded_message_size msg *)
          repeat destruct_one_match; logical_simplify; subst; lia. }
        { (* padder_byte_index <= padded_message_size msg *)
          repeat destruct_one_match; logical_simplify; subst; try lia;
          prove_by_zify. }
        { (* t <= 64 *)
          repeat destruct_one_match; logical_simplify; subst; lia. }
        { (* ready = (count <? 16)%N *)
          repeat destruct_one_match; logical_simplify; subst;
          repeat lazymatch goal with
                 | |- context [N.leb ?x ?y] => destr (N.leb x y); try lia
                 | |- context [N.ltb ?x ?y] => destr (N.ltb x y); try lia
                 end. }
        { (* digest = fold_left (SHA256.sha256_step msg)
                                (seq 0 completed_block_index) SHA256.H0 *)
          destruct done; logical_simplify; subst; boolsimpl.
          { cbn [Nat.eqb]. rewrite ?Nat.eqb_refl in *. natsimpl.
            destr (padded_message_size msg <? 64); logical_simplify; subst; [ lia | ].
            repeat destruct_one_match; logical_simplify; subst; try lia; reflexivity. }
          { destr fifo_data_valid;
            repeat (destruct_one_match; logical_simplify; subst; try lia; try reflexivity).
            all:repeat (destruct_one_match_hyp; logical_simplify; subst;
                        try lia; try reflexivity).
            all:lazymatch goal with
                | H : ?x = ?x / ?y * ?y |- context [(?x + ?z) / ?y] =>
                  rewrite H; rewrite (Nat.div_add_l (x / y) y) by lia;
                    rewrite ?Nat.div_small by lia; rewrite <-?H
                end.
            all:natsimpl.
            all:try reflexivity.
            all:lazymatch goal with
                | |- fold_left _ _ _ = fold_left _ _ _ =>
                  eapply fold_left_ext_In; intros *;
                    rewrite in_seq; intros
                end.
            all:rewrite sha256_step_truncate by prove_by_zify.
            all:reflexivity. } }
        { (* (if msg_complete
             then length msg <= padder_byte_index
             else padder_byte_index = length msg) *)
          repeat (destruct_one_match; logical_simplify; subst; try lia);
          cbv [new_msg_bytes]; length_hammer. }
        { (* (if done then ...  else True) *)
          Eval compute in "At abstract"%string.
          abstract ( 
          destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
            try discriminate; boolsimpl;
          rewrite ?Tauto.if_same; try tauto;
          repeat (destruct_one_match; logical_simplify; subst; try lia);
          repeat (destruct_one_match_hyp; logical_simplify; subst; try lia);
          boolsimpl_hyps;
          repeat lazymatch goal with
                     | H : (Nat.eqb ?x ?y) = true |- _ => apply Nat.eqb_eq in H; subst; try lia
                     end;
          prove_by_zify). }
        { (* clause that depends on count; in this case next count will always be <= 15 *)

          lazymatch goal with
          | |- if (?x <=? 15)%N then _ else _ =>
            assert (x <= 15)%N by (clear; repeat destruct_one_match; lia);
            destr (x <=? 15)%N; [ | lia ]
          end.
          ssplit.
          { (* skipn (16 - N.to_nat count) block
              = List.slice 0%N (SHA256.padded_msg msg)
                           (padder_block_index * 16) (N.to_nat count) *)
            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
              try discriminate; boolsimpl.
            all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
            all:repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:compute_expr (N.to_nat 1); cbn [N.to_nat]; natsimpl.
            all:push_skipn; try reflexivity.
            all:repeat lazymatch goal with
                       | H : ?x = ?x / ?y * ?y |- context [(?x + ?z) / ?y] =>
                         rewrite H; rewrite (Nat.div_add_l (x / y) y) by lia;
                           rewrite ?Nat.div_small by lia; rewrite <-?H
                       end.
            all:natsimpl.
            all:rewrite ?tl_app by (intro; subst; cbn [length] in *; discriminate).
            all:fold denote_type.
            all:change (denote_type sha_word) with N.
            all:push_skipn; push_length.
            all:push_skipn; listsimpl.
            all:rewrite slice_map_nth; cbn [seq List.map].
            (* structure already matches; use prove_by_zify for nat arguments *)
            all:repeat (f_equal; lazymatch goal with
                                 | |- @eq nat _ _ => prove_by_zify
                                 | _ => idtac
                                 end). }
          { (* padder_byte_index mod 64 = N.to_nat count * 4 *)
            repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:try prove_by_zify.
            all:repeat (destruct_one_match_hyp; logical_simplify; subst; try lia). }
          { (* (if (padder_byte_index <? 64) then t = 0 else t = 64) *)
            repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:repeat (destruct_one_match_hyp; logical_simplify; subst; try lia). }
          { (* inner_byte_index = padder_block_index * 64 *)
            repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:try prove_by_zify. } } }

          Eval compute in "At  0 < count <= 15 (padder running) "%string.
        { (* 0 < count <= 15 (padder running) *)
          destr (17 =? count)%N; [lia|].
          destr (16 =? count)%N; [lia|].
          ssplit.
          {
            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
              try discriminate; boolsimpl.
            all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
            all:repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:try prove_by_zify.
          }
          {
            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
              try discriminate; boolsimpl.
            all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
            all:repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:try prove_by_zify.
          }
          {
            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
              try discriminate; boolsimpl.
            all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
            all:repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:try prove_by_zify.
          }

          {
            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
              try discriminate; boolsimpl.
            all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
            all:repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:repeat match goal with
                | |- context [ (?X <=? ?Y)%N ] => destr (X <=? Y)%N
                | |- context [ (?X <? ?Y)%N ] => destr (X <? Y)%N
                end; try lia.
          }
          {

            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
              try discriminate; boolsimpl.
            all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
            {
              repeat (destruct_one_match; logical_simplify; subst; try lia); try reflexivity.
              all:try (exfalso; prove_by_zify).

              all:try lazymatch goal with
                  | H : ?x = ?x / ?y * ?y |- context [(?x + ?z) / ?y] =>
                    rewrite H; rewrite (Nat.div_add_l (x / y) y) by lia;
                      rewrite ?Nat.div_small by lia; rewrite <-?H
                  end.
              all:match goal with
                  | |- context [(?x + 4) / ?y] =>
                    replace ((x + 4)/y) with (x/y) by prove_by_zify
                  | |- context [(?x + 4)/ ?y - 1] =>
                    replace ((x + 4)/y - 1) with (x/y) by prove_by_zify
                  end.
              all:natsimpl.
              all:try reflexivity.
              all:try lazymatch goal with
                  | |- fold_left _ _ _ = fold_left _ _ _ =>
                    eapply fold_left_ext_In; intros *; rewrite in_seq;
                      intros
                  end.
              all:try now rewrite sha256_step_truncate by prove_by_zify.
            }
            {
              repeat (destruct_one_match; logical_simplify; subst; try lia); try reflexivity.
              all:destr (padder_byte_index =? padded_message_size msg); logical_simplify; subst; try lia.
              all:try (exfalso; prove_by_zify).

              all:try lazymatch goal with
                  | H : ?x = ?x / ?y * ?y |- context [(?x + ?z) / ?y] =>
                    rewrite H; rewrite (Nat.div_add_l (x / y) y) by lia;
                      rewrite ?Nat.div_small by lia; rewrite <-?H
                  end.
              all:match goal with
                  | |- context [(?x + 4) / ?y] =>
                    replace ((x + 4)/y) with (x/y) by prove_by_zify
                  | |- context [(?x + 4)/ ?y - 1] =>
                    replace ((x + 4)/y - 1) with (x/y) by prove_by_zify
                  end.
              all:natsimpl.
              all:try reflexivity.
              all:try lazymatch goal with
                  | |- fold_left _ _ _ = fold_left _ _ _ =>
                    eapply fold_left_ext_In; intros *; rewrite in_seq;
                      intros
                  end.
              all:try now rewrite sha256_step_truncate by prove_by_zify.
            }
            {
              repeat (destruct_one_match; logical_simplify; subst; try lia); try reflexivity.
              all:destr (padder_byte_index =? padded_message_size msg); logical_simplify; subst; try lia.
              all:try (exfalso; prove_by_zify).

              all:try lazymatch goal with
                  | H : ?x = ?x / ?y * ?y |- context [(?x + ?z) / ?y] =>
                    rewrite H; rewrite (Nat.div_add_l (x / y) y) by lia;
                      rewrite ?Nat.div_small by lia; rewrite <-?H
                  end.
              all:match goal with
                  | |- context [(?x + 4) / ?y] =>
                    replace ((x + 4)/y) with (x/y) by prove_by_zify
                  | |- context [(?x + 4)/ ?y - 1] =>
                    replace ((x + 4)/y - 1) with (x/y) by prove_by_zify
                  end.
              all:natsimpl.
              all:try reflexivity.
              all:try lazymatch goal with
                  | |- fold_left _ _ _ = fold_left _ _ _ =>
                    eapply fold_left_ext_In; intros *; rewrite in_seq;
                      intros
                  end.
              all:try now rewrite sha256_step_truncate by prove_by_zify.
            }
          }
          {
            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
              try discriminate; boolsimpl.
            all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
            all:repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:repeat match goal with
                | |- context [ (?X <=? ?Y)%N ] => destr (X <=? Y)%N
                | |- context [ (?X <? ?Y)%N ] => destr (X <? Y)%N
                end; try lia.
            all: cbn [new_msg_bytes]; push_length; lia.
          }
          {
            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
              try discriminate; boolsimpl.
            all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
            all:repeat (destruct_one_match; logical_simplify; subst; try lia).
            all:repeat match goal with
                | |- context [ (?X <=? ?Y)%N ] => destr (X <=? Y)%N
                | |- context [ (?X <? ?Y)%N ] => destr (X <? Y)%N
                end; try lia.
            all: cbn [new_msg_bytes]; push_length; lia.
          }

          boolsimpl.
          destr (padder_byte_index =? padded_message_size msg);
            destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
            try discriminate; boolsimpl.

          all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
          all:try (destruct_one_match; logical_simplify; subst; lia).
          all:natsimpl.
          all:push_skipn; try reflexivity.

          all:repeat (destruct_one_match; logical_simplify; subst; try lia).
          all:try (exfalso; prove_by_zify).
          all:ssplit;try lia.
          all:try(destr (length msg <? 64); lia).
          all:try(destr (padder_byte_index <? 64);lia).
          all:try prove_by_zify.
          all:repeat (destruct_one_match_hyp; logical_simplify; subst; try lia).
          all:try prove_by_zify.

          all:natsimpl.
          all:rewrite ?tl_app by (intro; subst; cbn [length] in *; discriminate).
          all:fold denote_type.
          all:change (denote_type sha_word) with N.
          all:push_skipn; push_length.
          all:push_skipn; listsimpl.
          all:replace (S (16 - N.to_nat ((count + 1) mod 64)%N)) with (16 - N.to_nat count) by prove_by_zify.
          all:replace ((count + 1) mod 64)%N with (count + 1)%N by prove_by_zify.
          all:autorewrite with Nnat.
          all:try rewrite H25; try reflexivity.
          all:push_skipn.
          all:try replace ((length msg + 4) / 64*16)  with (length msg / 64 * 16) by prove_by_zify.
          all:try replace (N.to_nat count + 1) with (S (N.to_nat count)) by lia.
          all:try assert (count = 15)%N by prove_by_zify; subst.
          all:try replace ( (16 - N.to_nat 15)) with 1 in * by lia.
          all:try match goal with
                  | H: skipn 1 _ = _ |- _ => rewrite skipn_1 in H
                  end.
Eval compute in "At abstract ".
          all: abstract ( try rewrite H25;
          try rewrite <-slice_snoc;
          try assert (padder_byte_index mod 64 = 60) by lia;
          try assert (padder_byte_index = (padder_byte_index / 64) * 64 + 60) by prove_by_zify;
          try rewrite slicen_padded_msg_truncate;
          f_equal; f_equal;
          try prove_by_zify;
          f_equal; try prove_by_zify).
        }

        {
Eval compute in "At abstract ".
          abstract (
          destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
            try discriminate; boolsimpl;
          rewrite ?Tauto.if_same in *; cbn [Nat.eqb];
          repeat (destruct_one_match; logical_simplify; subst; try lia);
          ssplit; try reflexivity; try lia; try prove_by_zify).
        }
        {
          destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
            try discriminate; boolsimpl.
          all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
          all:repeat (destruct_one_match; logical_simplify; subst; try lia).
          all:destr(17 =? count)%N; try lia.
          all:try destr (padder_byte_index =? 0); try lia.
          all:try destr (t =? 63); try lia.
          all: destruct done; destr (count =? 0)%N; try lia.
          all: ssplit; try reflexivity; try lia; try prove_by_zify.
          all: try match goal with
               | |- false = ?X => destr X; lia
               end.
          all: replace (16 - N.to_nat 0) with 16 by lia.
          all: try rewrite Tauto.if_same in E4; try lia.
          all: try (destr (length msg =? 0); lia).
          all: try rewrite skipn_all2 by lia; try reflexivity.
          {
            rewrite fold_left_sha256_step_alt_firstn.
            replace ( S (padder_byte_index / 64 - 1) ) with (padder_byte_index / 64) in * by prove_by_zify.
            apply H30.
            now rewrite fold_left_sha256_step_alt_firstn'
                with (i:=padder_byte_index / 64) (j:=padder_byte_index / 64 - 1) by prove_by_zify.
          }
          {
            rewrite fold_left_sha256_step_alt_firstn.
            destr (length msg =? 0); try lia.
            rewrite H30 by
              now rewrite <- fold_left_sha256_step_alt_firstn' by prove_by_zify.
            now replace (S (length msg / 64 - 1)) with (length msg / 64) by prove_by_zify.
          }
        }
      }
    }

  Eval compute in "Closing sha256 invariant proof".

Qed.

(* NOTE: To show CI progress *)
Check sha256_invariant_preserved.
Print Debug GC.
Optimize Heap.
Print Debug GC.


Lemma sha256_add_mod_bounded x y: (SHA256.add_mod x y < 2 ^ 32)%N.
Proof.
  cbv [SHA256.add_mod SHA256.w].
  apply N.mod_upper_bound; cbn; lia.
Qed.

Lemma fold_left_exists_final {A} {B} f (l: list A) (i: B):
  l <> [] -> exists x acc, fold_left f l i = f x acc.
Proof.
  intros.
  destruct l; [congruence|].
  revert i a H.
  induction l;
  [eexists; eexists; reflexivity|].
  intros.
  specialize (IHl (f i a0) a (ltac:(congruence))).
  inversion IHl.
  inversion H0.
  eexists. eexists.
  rewrite fold_left_cons.
  apply H1.
Qed.

Lemma Forall2_implies_Forall_map2 {A B C} r (f: A -> B -> C) l1 l2:
  Forall2 (fun x y => r (f x y)) l1 l2 ->
  Forall r (List.map2 f l1 l2).
Proof.
  intros.
  revert l2 H.
  induction l1.
  { intros. inversion H. constructor. }
  { intros.  destruct l2.
    { constructor. }
    constructor.
    { inversion H. apply H3. }
    { apply IHl1. inversion H. apply H5. }
  }
Qed.

Lemma sha256_output_correct : output_correct sha256.
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
  intros (((((msg, msg_complete), padder_byte_index), inner_byte_index), t), cleared).
  intros; logical_simplify; subst.

  rewrite step_sha256_simplified_eq. cbv [step_sha256_simplified]. cbn [fst snd].

  (* A whole bunch of assertions about the properties of padded_message_size
     related to all 3 possible next messages *)
  pose proof padded_message_size_mono
       msg (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_bytes_longer_than_input msg.
  pose proof padded_message_bytes_longer_than_input
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_bytes_longer_than_input
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof min_padded_message_size msg.
  pose proof min_padded_message_size
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof min_padded_message_size
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_size_modulo msg.
  pose proof padded_message_size_modulo
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_size_modulo
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).

  lazymatch goal with
  | H : sha256_padder_invariant ?state ?repr
    |- context [step sha256_padder ?state ?input] =>
    assert (precondition sha256_padder input repr)
  end.
  { simplify_spec sha256_padder. cbn [reset_repr sha256_padder_specification].
    destr cleared; logical_simplify; subst;
      [ destr fifo_data_valid; destr is_final; logical_simplify; subst;
        ssplit; solve [auto] | ].
    ssplit; [ assumption | ].
    destr fifo_data_valid; logical_simplify; subst; [ | tauto ].
    destr is_final; logical_simplify; subst; tauto. }

  use_correctness' sha256_padder.
  cbn [reset_repr sha256_padder_specification] in *.

  (* prove that inner precondition is satisfied *)
  lazymatch goal with
  | H : sha256_inner_invariant ?state ?repr
    |- context [step sha256_inner ?state ?input] =>
    assert (precondition sha256_inner input repr)
  end.
  { simplify_spec sha256_inner. cbn [reset_repr sha256_inner_specification].
    destr cleared; logical_simplify; subst;
      [ destr fifo_data_valid; destr is_final; logical_simplify; subst;
        ssplit; solve [auto] | ].
    rewrite fold_left_sha256_step_alt_firstn.
    all:destr (t =? 64); logical_simplify; subst; try lia.
    all:destr (count <=? 15)%N; logical_simplify; subst.
    all:destr (count =? 16)%N; logical_simplify; subst; try lia.
    all:repeat (destruct_one_match; logical_simplify; subst; try lia).
    all:repeat lazymatch goal with
               | H : (Nat.eqb ?x ?y) = false |- _ => apply Nat.eqb_neq in H
               end.
    all:try (destr (padder_byte_index <? 64); logical_simplify; subst; [ | lia ]).
    all:rewrite ?Nat.div_mul, ?Nat.div_small in * by lia.
    all:try reflexivity.
    all:try discriminate.
    all:natsimpl.
    all:repeat lazymatch goal with
               | |- context [(?x + ?y) / ?y] => replace ((x + y) / y) with (x / y + 1) by prove_by_zify
               | |- context [S (?x - 1)] => replace (S (x - 1)) with x by prove_by_zify
               end.
    all:natsimpl.
    all:try (destr (inner_byte_index + 64 =? 64); logical_simplify; subst; lia).
    all:lazymatch goal with
        | |- _ /\ _ /\ _ => ssplit; [ reflexivity | | length_hammer ]
        | _ => idtac
        end.
    all:rewrite ?firstn_slice_app by (push_length; prove_by_zify).
    all:lazymatch goal with
        | |- fold_left _ _ _ = fold_left _ _ _ =>
          eapply fold_left_ext_In; intros *;
            rewrite in_seq; intros;
              rewrite !sha256_step_alt_firstn by lia;
              try reflexivity
        end. }

  use_correctness' sha256_inner.
  cbn [reset_repr sha256_inner_specification] in *.

  eexists.
  eexists.
  eexists.
  ssplit.
  { reflexivity. }
  { destruct clear; [reflexivity|]; logical_simplify; subst.
    destruct cleared; logical_simplify; subst; cbn [fst snd].
    all: destr (0 <=? 15)%N; destr (16 =? 0)%N; destr (0 =? 0)%N; try lia; boolsimpl; logical_simplify; subst.
    { destruct fifo_data_valid; boolsimpl; reflexivity. }
    { destr (count <=? 15)%N; destr (16 =? count)%N; try lia; boolsimpl; logical_simplify; subst.
      all:repeat (destruct_one_match; logical_simplify; subst; try lia).
      all:boolsimpl.

      all:repeat (match goal with
                  | |- context [ ?X =? ?Y ] => destr ( X =? Y); try lia
                  | |- context [ ?X <=? ?Y ] => destr ( X <=? Y); try lia
                  | |- context [ ( ?X =? ?Y )%N ] => destr ( X =? Y)%N; try lia
                  | |- context [ ( ?X <=? ?Y )%N ] => destr ( X <=? Y)%N; try lia
                  end; boolsimpl).
      all: try lia.
      all: repeat (destruct_one_match_hyp; logical_simplify; subst; try lia).
      all: try lia; try prove_by_zify.
    }
  }

  {
    destruct clear; [reflexivity|]; logical_simplify; subst.
    destruct cleared; logical_simplify; subst; cbn [fst snd].
    all: destr (0 <=? 15)%N; destr (16 =? 0)%N; destr (0 =? 0)%N; try lia; boolsimpl; logical_simplify; subst.
    { destruct fifo_data_valid; boolsimpl; reflexivity. }
    rewrite N.mod_small by (cbn; prove_by_zify).
    destr (count <=? 15)%N; try lia; boolsimpl; logical_simplify; subst.
    all: destr (16 =? count)%N; try lia; boolsimpl; logical_simplify; subst.
    all:repeat (destruct_one_match; logical_simplify; subst; try lia).
    all:boolsimpl.


    all:repeat (match goal with
                | |- context [ ?X =? ?Y ] => destr ( X =? Y); try lia
                | |- context [ ?X <=? ?Y ] => destr ( X <=? Y); try lia
                | |- context [ ( ?X =? ?Y )%N ] => destr ( X =? Y)%N; try lia
                | |- context [ ( ?X <=? ?Y )%N ] => destr ( X <=? Y)%N; try lia

                | H: context [ ?X =? ?Y ] |- _ => destr ( X =? Y); try lia
                | H: context [ ?X <=? ?Y ] |- _ => destr ( X <=? Y); try lia
                | H: context [ ( ?X =? ?Y )%N ] |- _ => destr ( X =? Y)%N; try lia
                | H: context [ ( ?X <=? ?Y )%N ] |- _ => destr ( X <=? Y)%N; try lia
                end; boolsimpl).
    all: try lia; try prove_by_zify.
    all: repeat (destruct_one_match_hyp; logical_simplify; subst; try lia).
    all: try lia; try prove_by_zify.
  }

  destruct clear; [reflexivity|]; logical_simplify; subst.
  destruct cleared; logical_simplify; subst; cbn [fst snd];
  destruct fifo_data_valid; boolsimpl; cbn [fst snd]; [reflexivity .. | ].
  destruct_one_match;[|reflexivity].

  cbv [SHA256.sha256 SHA256.w]; rewrite concat_digest_to_N_id; rewrite padded_message_length;
    replace (512 / N.to_nat 32) with 16 by prove_by_zify; cycle 1.
  { cbv [SHA256.sha256_step].

    assert (seq 0 (padded_message_size msg / 4 / 16) <> []).
    { assert (1 <= padded_message_size msg / 4 / 16) by prove_by_zify.
      apply length_pos_nonnil.
      length_hammer.
    }

    pose proof (fold_left_exists_final (fun (H0 : list N) (i : nat) =>
      List.map2 SHA256.add_mod H0
        (fold_left (SHA256.sha256_compress (SHA256.W msg i)) (seq 0 64) H0))
        (seq 0 (padded_message_size msg / 4 / 16)) SHA256.H0 H20) as Hff.
    logical_simplify.
    rewrite H22.

    remember (fold_left (SHA256.sha256_compress (SHA256.W msg x4)) (seq 0 64) x3) as X.
    clear.

    rename x3 into a.
    rename X into b.

    assert (forall {C} a b (f: N -> N -> C), List.map2 f a b =
      let sz := Nat.min (length a) (length b) in List.map2 f (List.resize 0%N sz a) (List.resize 0%N sz b)).
    { clear; intros.
      revert a.
      induction b.
      { intros a. destruct a; now cbn. }
      intros.
      destruct a0.
      { now cbn. }
      push_length.
      rewrite <- Min.succ_min_distr.
      cbn zeta.
      rewrite resize_cons.
      rewrite resize_cons.
      cbn [List.map2].
      rewrite IHb.
      reflexivity.
    }

    rewrite H; clear H.
    cbn zeta.

    apply Forall2_implies_Forall_map2.
    revert a.
    induction b.
    { intros. destruct a; now cbn. }
    intros.
    destruct a0.
    { now cbn. }
    push_length.
    rewrite <- Min.succ_min_distr.
    cbn zeta.
    rewrite resize_cons.
    rewrite resize_cons.
    constructor.
    { apply sha256_add_mod_bounded. }
    apply IHb.
  }
  { length_hammer. }

  destruct_one_match.
  { destr (inner_byte_index =? 0).
    { repeat (match goal with
                  | H: context [ ?X =? ?Y ] |- _ => destr ( X =? Y); try lia
                  | H: context [ ?X <=? ?Y ] |- _ => destr ( X <=? Y); try lia
                  | H: context [ ( ?X =? ?Y )%N ] |- _ => destr ( X =? Y)%N; try lia
                  | H: context [ ( ?X <=? ?Y )%N ] |- _ => destr ( X <=? Y)%N; try lia
                  end; boolsimpl).
    }
    destr (16 =? count)%N; try prove_by_zify.
    destr (if if t =? 64 then true else false then true else t =? 63); [|prove_by_zify].
    destr done; destr (count <=? 15)%N; destr (count =? 16)%N; logical_simplify; subst; try prove_by_zify.

    all: repeat (match goal with
                  | H: context [ ?X =? ?Y ] |- _ => destr ( X =? Y); try lia
                  | H: context [ ?X <=? ?Y ] |- _ => destr ( X <=? Y); try lia
                  | H: context [ ( ?X =? ?Y )%N ] |- _ => destr ( X =? Y)%N; try lia
                  | H: context [ ( ?X <=? ?Y )%N ] |- _ => destr ( X <=? Y)%N; try lia
                  end; boolsimpl); try prove_by_zify.
  }
  all: repeat (match goal with
              | H: context [ ?X =? ?Y ] |- _ => destr ( X =? Y); try lia
              | H: context [ ?X <=? ?Y ] |- _ => destr ( X <=? Y); try lia
              | H: context [ ( ?X =? ?Y )%N ] |- _ => destr ( X =? Y)%N; try lia
              | H: context [ ( ?X <=? ?Y )%N ] |- _ => destr ( X <=? Y)%N; try lia
              end; boolsimpl); try prove_by_zify.
  all: logical_simplify; subst.
  { rewrite <- E4. reflexivity. }
  do 2 f_equal.
  prove_by_zify.
Qed.
