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

Module Nat.
  Definition ceiling (a b : nat) :=
    a / b + if a mod b =? 0 then 0 else 1.
End Nat.

(* length of the padded message (in bytes) is the smallest number of 512-bit
   (64-byte) blocks that can fit the message plus 9 more bytes (one for the
   extra 1 bit and 8 for the length -- extra 1 bit needs a full byte because
   message must be byte-aligned) *)
Definition padded_message_size (msg : list byte) : nat :=
  (Nat.ceiling (length msg + 9) 64) * 64.

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
  (* ...and if msg_complete is true, we must have processed the whole message *)
  /\ (if msg_complete then length msg <= index else index = length msg)
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
          then index = padded_message_size msg
          else index = 0 /\ msg = [])
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
       expected_padder_state msg msg_complete padder_done index = padder_waiting_value
       (* ...then message must not be complete *)
       /\ msg_complete = false
       (* ...and final_length (if given) must be in range *)
       /\ (if is_final
          then (1 < final_length <= 4)%N
          else True)
       (* ...and data value must be in range *)
       /\ (if is_final
          then data < 2 ^ (8 * final_length)
          else data < 2 ^ 32)%N
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
Lemma step_bvconcat {n m} (x : denote_type (BitVec n)) (y : denote_type (BitVec m)) :
  step (bvconcat (n:=n) (m:=m)) tt (x, (y, tt))
  = (tt, N.lor (N.shiftl (N.land x (N.ones (N.of_nat n))) (N.of_nat m))
               (N.land y (N.ones (N.of_nat (n + m))))).
Proof.
  cbv [bvconcat]. stepsimpl. f_equal.
  apply N.bits_inj; intro i. push_Ntestbit.
  rewrite Nat2N.inj_add.
  destruct_one_match; push_Ntestbit; boolsimpl; [ | reflexivity ].
  destr (i <? N.of_nat m)%N; push_Ntestbit; boolsimpl; reflexivity.
Qed.
Hint Rewrite @step_bvconcat using solve [eauto] : stepsimpl.

(* TODO: move *)
Lemma step_bvslice {n start len} (x : denote_type (BitVec n)) :
  step (bvslice (n:=n) start len) tt (x, tt)
  = (tt, N.land (N.shiftr x (N.of_nat start)) (N.ones (N.of_nat len))).
Proof. reflexivity. Qed.
Hint Rewrite @step_bvslice using solve [eauto] : stepsimpl.

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
Lemma padded_message_bytes_length msg :
  length (SHA256.padded_msg_bytes msg) = padded_message_size msg.
Admitted.
(* TODO: move *)
Lemma padded_message_bytes_longer_than_input msg :
  length msg + 9 <= padded_message_size msg.
Admitted.
Lemma padded_message_longer_than_input msg :
  length (BigEndianBytes.bytes_to_Ns 4 msg) < length (SHA256.padded_msg msg).
Admitted.
(* TODO: move *)
Lemma min_padded_message_size msg : 64 <= padded_message_size msg.
Admitted.
(* TODO: move *)
Lemma padded_message_size_modulo msg : padded_message_size msg mod 64 = 0.
Admitted.
(* TODO: move *)
Lemma padded_message_min_length msg : 16 <= length (SHA256.padded_msg msg).
Admitted.
(* TODO: move *)
(* Adding data cannot decrease padded message size *)
Lemma padded_message_size_mono msg data :
  padded_message_size msg <= padded_message_size (msg ++ data).
Admitted.

(* TODO: move *)
Local Ltac prove_by_zify :=
  Zify.zify;
  (* extra step because zify fails to zify Nat.modulo and Nat.div *)
  rewrite ?mod_Zmod, ?div_Zdiv in * by lia;
  Zify.zify; Z.to_euclidean_division_equations; lia.

(* helper lemma for modular arithmetic *)
Lemma increment_offset (offset index : N) :
  (offset * 4 = index mod 64)%N ->
  ((offset + 1) mod 16 * 4 = (index + 4) mod 64)%N.
Proof. intros. prove_by_zify. Qed.

(* TODO: move *)
(* helper lemma for modular arithmetic *)
Lemma ceiling_add_same a b c :
  1 < c < b - 1 -> a mod b <= b - c ->
  Nat.ceiling (a + c) b = Nat.ceiling (a + 1) b.
Proof.
  (* proof sketch:
     Since a mod b <= b - c and 1 < c < b - 1, it follows that:
           (1) (a + 1) mod b <> 0
           (2) (a + c) mod b = 0 iff a mod b = b - c
           (3) (a + c) / b = (a + 1) / b + if (a mod b = b - c) then 1 else 0

     Proof of (1):
           (a + 1) mod b = (a mod b + 1) mod b
                         = a mod b + 1 (because a mod b + 1 <= (b - c) + 1 < b)
                         > 0

     Proof of (2):
           case 1 (a mod b <> b - c): same logic as (1) proves (a + c) mod b <> 0
           case 1 (a mod b = b - c):
             (a + c) mod b = (a mod b + c) mod b
                           = (b - c + c) mod b
                           = 0

     Proof of (3):
           (a + c) / b = (a + 1 + (c - 1)) / b
                       = ((a + 1) / b * b + (a + 1) mod b + (c - 1)) / b
                       = (a + 1) / b + (a mod b + 1 + (c - 1)) / b
                       = (a + 1) / b + (a mod b + c) / b
                       = (a + 1) / b + if (a mod b = b - c) then 1 else 0

     Therefore:
        Nat.ceiling (a + 1) b
                    = (a + 1) / b + if (a + 1) mod b =? 0 then 0 else 1
                    = (a + 1) / b + 1

        Nat.ceiling (a + c) b
                    = (a + c) / b + if (a + c) mod b =? 0 then 0 else 1
                    = (a + c) / b + if (a mod b = b - c) then 0 else 1
                    = (a + 1) / b + if (a mod b = b - c) then 1 else 0
                                  + if (a mod b = b - c) then 0 else 1
                    = (a + 1) b + 1
  *)
Admitted.

(* TODO: move *)
(* helper lemma for modular arithmetic *)
Lemma ceiling_add_diff a b c :
  0 < b -> 0 < c < b -> b - c < a mod b ->
  Nat.ceiling (a + c) b = Nat.ceiling a b + 1.
Proof.
  (* proof sketch:
     Since (b - c < a mod b) and 0 < c, it follows that:
           0 < a mod b + c < b
           a mod b <> 0

     Therefore:
           (a + c) mod b = (a mod b + c) mod b
                         =  a mod b + c
           (a + c) / b = (a / b * b + a mod b + c) / b
                       =  a / b + (a mod b + c) / b
                       =  a / b

     Nat.ceiling (a + c) b
                 = (a + c) / b + (if (a + c) mod b =? 0 then 0 else 1)
                 = (a + c) / b + 1
                 = a / b + 1

     Nat.ceiling a b
                 = a / b + if a mod b =? 0 then 0 else 1
                 = a / b + 1
  *)
Admitted.

(* TODO: move *)
Lemma ceiling_range a b :
  0 < b -> 0 < a ->
  Nat.ceiling a b * b - b < a <= Nat.ceiling a b * b.
Admitted.

Lemma expected_padder_state_cases msg (msg_complete padder_done : bool) index :
  index < padded_message_size msg ->
  index mod 4 = 0 ->
  (if msg_complete then length msg <= index else index = length msg) ->
  ( (* either we're in the waiting state and the padder's expected output at
       index i is just the ith byte of the message *)
    (expected_padder_state msg msg_complete padder_done index = padder_waiting_value
     /\ (if msg_complete then padder_done = true else True)
     /\ nth index (SHA256.padded_msg_bytes msg) x00 = nth index msg x00)
    (* ...or we're in the emit_bit state and the padder's expected output at
       index i is 0x80 *)
    \/ (expected_padder_state msg msg_complete padder_done index = padder_emit_bit_value
       /\ msg_complete = true
       /\ padder_done = false
       /\ index = length msg
       /\ index < padded_message_size msg - 8
       /\ nth index (SHA256.padded_msg_bytes msg) x00 = x80)
    (* ...or we're in the flushing state and the padder's expected output at
       index i is 0x00 *)
    \/ (expected_padder_state msg msg_complete padder_done index = padder_flushing_value
       /\ msg_complete = true
       /\ padder_done = false
       /\ index < padded_message_size msg - 8
       /\  nth index (SHA256.padded_msg_bytes msg) x00 = x00)
    (* ...or we're in the writing_length state and the padder's expected output
       at index i part of the length *)
    \/ (expected_padder_state msg msg_complete padder_done index = padder_writing_length_value
       /\ msg_complete = true
       /\ padder_done = false
       /\ padded_message_size msg - 8 <= index
       /\  nth index (SHA256.padded_msg_bytes msg) x00
          = nth (index - (padded_message_size msg - 8))
                (BigEndianBytes.N_to_bytes 8 (N.of_nat (length msg))) x00)).
Proof.
  intros.
  pose proof padded_message_bytes_longer_than_input msg.
  pose proof padded_message_size_modulo msg.
  assert (padded_message_size msg - 64 < length msg + 9 <= padded_message_size msg).
  { apply ceiling_range; lia. }
  (* helpful assertion for the case that length fits in the same block as
     message *)
  assert ((length msg + 1) mod 64 <= 56 ->
          padded_message_size msg - 64 <= length msg + 1).
  { cbv [padded_message_size] in *. intros.
    replace (length msg + 9) with (length msg + 1 + 8) by lia.
    rewrite ceiling_add_same with (c:=8) by lia.
    pose proof ceiling_range (length msg + 1 + 1) 64 ltac:(lia) ltac:(lia).
    lia. }
  (* helpful assertion for the case that length does not fit in the same block
     as message *)
  assert (56 < (length msg + 1) mod 64 ->
          padded_message_size msg - 64 >= length msg + 1).
  { cbv [padded_message_size] in *. intros.
    replace (length msg + 9) with (length msg + 1 + 8) by lia.
    rewrite ceiling_add_diff with (c:=8) by lia.
    pose proof ceiling_range (length msg + 1) 64 ltac:(lia) ltac:(lia).
    lia. }
  cbv [expected_padder_state]; repeat destruct_one_match; subst; try lia;
    cbv [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
               padder_emit_bit_value padder_writing_length_value].
  all:repeat lazymatch goal with
             | |- ?P \/ ?Q =>
               first [ let H := fresh in
                       assert (~ P) as H by (intro; logical_simplify; discriminate);
                       clear H; right
                     | left ]
             end.
  all:ssplit; try reflexivity; try lia.
  all:lazymatch goal with
        | |- context [nth] => idtac
        |  _ =>
           (* solve all other goals with modular arithmetic automation *)
           prove_by_zify
      end.

  (* remaining goals all about matching up indices in spec with expected expression *)
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
       then
         if padder_done
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
                 then if is_final
                      then firstn (N.to_nat final_length) (BigEndianBytes.N_to_bytes 4 data)
                      else BigEndianBytes.N_to_bytes 4 data
                 else []
            else if data_valid
                 then if is_final
                      then msg ++ (firstn (N.to_nat final_length)
                                          (BigEndianBytes.N_to_bytes 4 data))
                      else msg ++ BigEndianBytes.N_to_bytes 4 data
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
            else new_index =? padded_message_size new_msg
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
    pose proof min_padded_message_size msg.
    lazymatch goal with
    | |- context [msg ++ firstn ?n ?data] =>
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
      repeat destruct_one_match; [ reflexivity | | ];
      logical_simplify; subst.
      all:symmetry; apply Nat.eqb_neq.
      all:let data := lazymatch goal with |- context [?msg ++ ?data] => data end in
          pose proof padded_message_bytes_longer_than_input (msg ++ data).
      all:autorewrite with push_length in *; lia. }
    { (* index is past or at end of message if is_final is true, otherwise equal
         to length of message *)
      repeat destruct_one_match; logical_simplify; subst; push_length; try lia. }
    { (* if output is valid, then new index must be at least 4 *)
      repeat destruct_one_match; lia. }
    { (* output matches spec *)
      (* need step bvconcat + step bvslice, use expected state cases *)
      admit. }
    { cbv [expected_padder_state] in *.
      destruct padder_done, out_valid, is_final; logical_simplify; subst.
      all:repeat (destruct_one_match_hyp; try discriminate).
      all:repeat destruct_one_match; try lia. }
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
      all:rewrite ?Nat.mod_small by lia.
      all:repeat (destruct_one_match; try discriminate; try lia); subst.
      all:try (specialize (Hincr ltac:(assumption)); cbn in Hincr).
      all:try lia; prove_by_zify. } }
  { (* Case for handling invalid data:
       consumer_ready=true
       clear=false
       data_valid=false
     *)
    pose proof length_bytes_to_Ns_upper_bound 4 msg.
    pose proof padded_message_longer_than_input msg.
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
      admit. (* prove that looking for writing_length state and offset = 15 is
                the same as waiting for the end of the expected message *)
    }
    { (* if message is complete, index is past or at end of message; otherwise,
         index = length of message *)
      repeat destruct_one_match; logical_simplify; subst; push_length; lia. }
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
    { (* entire clause for what happens if we're done or not done *)
      destruct padder_done;
        logical_simplify; subst; rewrite ?N.eqb_refl;
          cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
                     padder_emit_bit_value padder_writing_length_value
                     negb andb orb];
          [ ssplit; reflexivity | ].
      pose proof
           expected_padder_state_cases msg msg_complete false index
           ltac:(eauto) ltac:(eauto) ltac:(eauto) as padder_state_cases.
      let H := fresh in
      destruct padder_state_cases as [H|[H|[H|H]]];
        logical_simplify; subst;
        lazymatch goal with H : expected_padder_state _ _ _ _ = _ |- _ =>
                            rewrite H in * end.
      all:cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
                     padder_emit_bit_value padder_writing_length_value
                     negb andb orb].
      all:repeat lazymatch goal with
                 | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia; [ ]
                 end.
      { (* padder_waiting case *)
        destruct msg_complete; try discriminate; ssplit; try lia; [ ].
        destruct (index =? padded_message_size msg); try lia; [ ].
        reflexivity. }
      { (* padder_emit_bit case *)
        ssplit; [ lia .. | | ].
        { rewrite Nat2N.inj_add.
          apply increment_offset; lia. }
        { admit. (* state transition *) } }
      { (* padder_flushing case *)
        ssplit; [ lia .. | | ].
        { rewrite Nat2N.inj_add.
          apply increment_offset; lia. }
        { admit. (* state transition *) } }
      { (* padder_writing_length case *)
        pose proof padded_message_size_modulo msg.
        assert (if (current_offset =? 15)%N
                then index = padded_message_size msg - 4
                else current_offset = 14%N /\ index = padded_message_size msg - 8)
          by (destruct_one_match; prove_by_zify).
        destr (current_offset =? 15)%N;
          logical_simplify; subst;
            cbn [N.eqb Pos.eqb padder_waiting_value padder_flushing_value
                       padder_emit_bit_value padder_writing_length_value
                       negb andb orb].
        { ssplit; try lia; reflexivity. }
        { ssplit; [ lia .. | | ].
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
Admitted.
