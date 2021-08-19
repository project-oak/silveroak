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
Require Import Coq.NArith.NArith.
Require Import coqutil.Datatypes.List.
Require Import Coq.micromega.Lia. (* for list_eqb, remove if upstreamed *)
Require Import coqutil.Decidable. (* for list_eqb, remove if upstreamed *)
Require Import coqutil.Tactics.Tactics. (* for list_eqb, remove if upstreamed *)
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Expr.
Require Import Cava.Semantics.
Require Import Cava.Types.
Require Import HmacSpec.SHA256.
Require Import HmacSpec.Tests.SHA256TestVectors.
Require Import HmacHardware.Sha256.
Import ListNotations.

(**** list boolean equality decider ****)

(* TODO: this may be upstreamed, remove if
   https://github.com/mit-plv/coqutil/pull/37 gets merged *)
Definition list_eqb {A} (aeqb : A -> A -> bool) {aeqb_spec:EqDecider aeqb} (x y : list A) : bool :=
  ((length x =? length y)%nat && forallb (fun xy => aeqb (fst xy) (snd xy)) (combine x y))%bool.

Lemma list_forallb_eqb_refl {A} (aeqb : A -> A -> bool) {aeqb_spec:EqDecider aeqb} ls :
  forallb (fun xy => aeqb (fst xy) (snd xy)) (combine ls ls) = true.
Proof.
  induction ls as [|x ?]; [ reflexivity | ].
  cbn [combine fst snd forallb]. rewrite IHls.
  destr (aeqb x x); subst; congruence || reflexivity.
Qed.

Lemma length_eq_forallb_eqb_false {A} (aeqb : A -> A -> bool) {aeqb_spec:EqDecider aeqb} x y :
  length x = length y -> x <> y ->
  forallb (fun xy => aeqb (fst xy) (snd xy)) (combine x y) = false.
Proof.
  revert y.
  induction x as [|x0 x]; destruct y as [|y0 y];
    cbn [length]; [ congruence | lia .. | ].
  intros. cbn [combine fst snd forallb].
  destr (aeqb x0 y0); [ | reflexivity ].
  rewrite IHx by congruence. reflexivity.
Qed.

Instance list_eqb_spec {A} (aeqb : A -> A -> bool) {aeqb_spec:EqDecider aeqb}
  : EqDecider (list_eqb aeqb).
Proof.
  cbv [list_eqb].
  induction x as [|x0 x]; destruct y as [|y0 y];
    cbn [length combine forallb Nat.eqb andb fst snd];
    try (constructor; congruence) ; [ ].
  destruct (IHx y); subst.
  { rewrite Nat.eqb_refl.
    rewrite list_forallb_eqb_refl by auto.
    destr (aeqb x0 y0); subst; constructor; congruence. }
  { destr (length x =? length y); cbn [andb];
    try (constructor; congruence); [ ].
    rewrite length_eq_forallb_eqb_false by auto.
    rewrite Bool.andb_false_r. constructor; congruence. }
Qed.

(**** Convert to/from circuit signals ****)

(* extra cycles to allow for padder synchronization after each block of true
   input; can be an overestimate *)
Definition extra_cycles : nat := 80.

(* convert test vector data into circuit input signals *)
Definition to_sha256_input (t : sha256_test_vector)
  : list (denote_type (input_of (var:=denote_type) sha256)) :=
  (* input must be divided into into 32-bit words *)
  let l := N.to_nat t.(l) in
  let nwords := l / 32 + (if l mod 32 =? 0 then 0 else 1) in
  (* separate bytes for the final word and bytes for non-final words *)
  let non_final_bytes := firstn ((nwords - 1) * 4) t.(msg_bytes) in
  let final_bytes := skipn ((nwords - 1) * 4) t.(msg_bytes) in
  (* convert bytes to words *)
  let non_final_words := BigEndianBytes.bytes_to_Ns 4 non_final_bytes in
  let final_bytes_padded := final_bytes ++ repeat Byte.x00 (4 - length final_bytes) in
  let final_word := BigEndianBytes.concat_bytes final_bytes_padded in
  let final_length := N.of_nat (length final_bytes) in
  (* create actual input signals *)
  let non_final_input : list (denote_type (input_of sha256)) :=
      (* fifo_data_valid=1, fifo_data, is_final=0, final_length=0, clear=0 *)
      List.map (fun data => (1, (data, (0, (0, (0, tt)))))%N) non_final_words in
  let final_input : denote_type (input_of sha256) :=
      (* fifo_data_valid=1, fifo_data, is_final=1, final_length=final_length,
         clear=0 *)
      (1, (final_word, (1, (final_length, (0, tt)))))%N in
  (* if input is multiple blocks long *before* padding, we need to add dummy
     inputs after each block to wait for the padder to be ready to accept input
     again *)
  let words_per_block := (512 / N.to_nat w) in
  let nblocks_non_final :=
      length (non_final_input) / words_per_block
      + if (length (non_final_input) mod words_per_block =? 0) then 0 else 1 in
  let nblocks_padded := length (SHA256.padded_msg t.(msg_bytes)) / words_per_block in
  let dummy_input : denote_type (input_of sha256) := (0, (0, (0, (0, (0, tt)))))%N in
  (* introduce dummy inputs between each block of 16 words in the input,
     including between non-final and final blocks if there is at least one
     non-final block *)
  let non_final_input_spaced :=
      flat_map
        (fun i => firstn words_per_block (skipn (words_per_block*i) non_final_input)
                      ++ repeat dummy_input extra_cycles)
        (seq 0 nblocks_non_final) in
  (* cycles to wait after input
     = cycles for padding (16 per post-padding block)
     + cycles for compression (64 per post-padding block)
     + extra_cycles *)
  let ndummy := ((64+16)*nblocks_padded + extra_cycles) in
  non_final_input_spaced ++ [final_input] ++ repeat dummy_input ndummy.

(* extract test result from circuit output signals *)
Definition from_sha256_output
           (out : list (denote_type (output_of (var:=denote_type) sha256)))
  : N :=
  let '(done, (digest, accept_input)) := last out default in
  BigEndianBytes.concat_bytes (concat_digest digest).

(* convert test vector data into input signals for padder *)
Definition to_sha256_padder_input (t : sha256_test_vector)
  : list (denote_type (input_of (var:=denote_type) sha256_padder)) :=
  (* For padder tests, we assume the consumer is always ready *)
  List.map
    (fun '(fifo_data_valid,(fifo_data,(is_final,(final_length,(clear,_))))) =>
       (* data_valid, data, is_final, final_length, consumer_ready, clear *)
       (fifo_data_valid,(fifo_data, (is_final, (final_length, (1%N, (clear, tt)))))))
    (to_sha256_input t).

Definition concat_words (n : nat) (ws : list N) : N :=
  fold_left (fun acc w => N.lor (N.shiftl acc (N.of_nat n)) (w mod 2 ^ N.of_nat n)) ws 0%N.

(* extract test result from padder output signals *)
Definition from_sha256_padder_output
           (out : list (denote_type (output_of (var:=denote_type) sha256_padder)))
  : N :=
  (* remove invalid output signals entirely, and extract data from signals *)
  let valid_out :=
      flat_map
        (fun '(out_valid, (data, (consumer_ready, done))) =>
           if (out_valid =? 0)%N
           then []
           else [data]) out in
  concat_words (N.to_nat w) valid_out.

(* extract all intermediate digests from circuit output signals *)
Definition intermediate_digests_from_sha256_output
           (out : list (denote_type (output_of (var:=denote_type) sha256)))
  : list (list N) :=
  let digests := List.map (fun '(done, (digest, accept_input)) => digest) out in
  (* remove repetitions of the same digest *)
  dedup (list_eqb N.eqb) digests.

(**** Run test vectors ****)

(* test the padder in isolation *)
Goal (let t := test1 in
      from_sha256_padder_output
        (simulate sha256_padder (to_sha256_padder_input t)) = t.(expected_padded_msg)).
Proof. vm_compute. reflexivity. Qed.

Goal (let t := test2 in
      from_sha256_padder_output
        (simulate sha256_padder (to_sha256_padder_input t)) = t.(expected_padded_msg)).
Proof. vm_compute. reflexivity. Qed.

(* test intermediate digests *)
Goal (let t := test1 in
      intermediate_digests_from_sha256_output
        (simulate sha256 (to_sha256_input t)) = H0 :: t.(expected_intermediate_digests)).
Proof. vm_compute. reflexivity. Qed.

Goal (let t := test2 in
      intermediate_digests_from_sha256_output
        (simulate sha256 (to_sha256_input t)) = H0 :: t.(expected_intermediate_digests)).
Proof. vm_compute. reflexivity. Qed.

(* Test the full circuit *)
Goal (let t := test1 in
      from_sha256_output (simulate sha256 (to_sha256_input t)) = t.(expected_digest)).
Proof. vm_compute. reflexivity. Qed.

Goal (let t := test2 in
      from_sha256_output (simulate sha256 (to_sha256_input t)) = t.(expected_digest)).
Proof. vm_compute. reflexivity. Qed.

Goal (let t := test3 in
      from_sha256_output (simulate sha256 (to_sha256_input t)) = t.(expected_digest)).
Proof. vm_compute. reflexivity. Qed.
