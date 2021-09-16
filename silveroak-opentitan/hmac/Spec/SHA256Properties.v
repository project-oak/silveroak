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

Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.Nat.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import HmacSpec.SHA256.
Import ListNotations.
Local Open Scope N_scope.

Local Ltac lia' := Zify.zify; Z.to_euclidean_division_equations; lia.
Local Ltac t := cbv [k]; lia'.

(* k is a solution to the equation:
     l + 1 + k = 448 (mod 512) *)
Lemma k_correct msg : (l msg + 1 + k msg) mod 512 = 448.
Proof. t. Qed.

(* Prove that k < 512 *)
Lemma k_small msg : k msg < 512.
Proof. t. Qed.

(* Prove that k is the smallest non-negative solution to the equation *)
Lemma k_smallest msg n : (l msg + 1 + n) mod 512 = 448 -> n >= k msg.
Proof. t. Qed.

(* Formula for the nth element of W (n > 15) *)
Lemma nth_W msg (i t : nat) :
  (t < 64)%nat ->
  nth t (SHA256.W msg i) 0 =
  if (t <? 16)%nat
  then SHA256.M msg t i
  else
    let W_tm2 := nth (t - 2) (SHA256.W msg i) 0 in
    let W_tm7 := nth (t - 7) (SHA256.W msg i) 0 in
    let W_tm15 := nth (t - 15) (SHA256.W msg i) 0 in
    let W_tm16 := nth (t - 16) (SHA256.W msg i) 0 in
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
                forall t, (t < n)%nat -> nth t W 0 = W_formula W t)
         (P:=fun W => nth t W 0 = W_formula W t);
    [ intros; ssplit; length_hammer
    | | intros; ssplit; logical_simplify; solve [auto] ].
  intros. autorewrite with natsimpl push_nth in *.
  logical_simplify. ssplit; [ length_hammer | ]. intros.
  lazymatch goal with H : (?t < S ?n)%nat |- context [nth ?t] =>
                      destr (t <? n)%nat; [ | replace t with n in * by lia ]
  end; subst W_formula; cbn beta zeta; push_nth; natsimpl;
    [ solve [auto] | ].
  destruct_one_match; push_nth; reflexivity.
Qed.

Lemma H0_length : length H0 = 8%nat.
Proof. reflexivity. Qed.
Hint Rewrite @H0_length using solve [eauto] : push_length.

Lemma sha256_compress_length msg i H t :
  length (sha256_compress msg i H t) = 8%nat.
Proof. reflexivity. Qed.
Hint Rewrite @sha256_compress_length : push_length.

Lemma fold_left_sha256_compress_length msg i H ts :
  length H = 8%nat ->
  length (fold_left (sha256_compress msg i) ts H) = 8%nat.
Proof.
  intros. apply fold_left_invariant with (I:=fun H => length H = 8%nat); auto.
Qed.
#[export] Hint Resolve fold_left_sha256_compress_length : length.

Lemma sha256_step_length msg H i :
  length H = 8%nat -> length (sha256_step msg H i) = 8%nat.
Proof.
  intro Hlen; cbv [sha256_step]. push_length.
  repeat (push_length || rewrite Hlen || rewrite fold_left_sha256_compress_length); lia.
Qed.
#[export] Hint Resolve sha256_step_length : length.

Lemma fold_left_sha256_step_length msg H idxs :
  length H = 8%nat -> length (fold_left (sha256_step msg) idxs H) = 8%nat.
Proof.
  intros. apply fold_left_invariant with (I:=fun H => length H = 8%nat); auto.
  intros; length_hammer.
Qed.
#[export] Hint Resolve fold_left_sha256_step_length : length.

(* length of the padded message (in bytes) is the smallest number of 512-bit
   (64-byte) blocks that can fit the message plus 9 more bytes (one for the
   extra 1 bit and 8 for the length -- extra 1 bit needs a full byte because
   message must be byte-aligned) *)
Definition padded_message_size (msg : list byte) : nat :=
  (Nat.ceiling (length msg + 9) 64) * 64.

Lemma padded_message_bytes_length msg :
  length (SHA256.padded_msg_bytes msg) = padded_message_size msg.
Proof.
  cbv [SHA256.padded_msg_bytes SHA256.padding padded_message_size].
  push_length. rewrite !Nat.ceiling_equiv. cbv [SHA256.k SHA256.l].
  destruct_one_match; prove_by_zify.
Qed.
Hint Rewrite @padded_message_bytes_length : push_length.

Lemma padded_message_bytes_longer_than_input msg :
  (length msg + 9 <= padded_message_size msg)%nat.
Proof.
  cbv [padded_message_size].
  pose proof Nat.ceiling_range (length msg + 9) 64 ltac:(lia) ltac:(lia).
  lia.
Qed.

Lemma min_padded_message_size msg : (64 <= padded_message_size msg)%nat.
Proof.
  cbv [padded_message_size].
  pose proof Nat.ceiling_range (length msg + 9) 64 ltac:(lia) ltac:(lia).
  lia.
Qed.

Lemma padded_message_size_modulo msg :
  (padded_message_size msg mod 64 = 0)%nat.
Proof. apply Nat.mod_mul. lia. Qed.

(* Adding data cannot decrease padded message size *)
Lemma padded_message_size_mono msg data :
  (padded_message_size msg <= padded_message_size (msg ++ data))%nat.
Proof.
  cbv [padded_message_size]. push_length.
  replace (length msg + length data + 9)%nat
    with (length msg + 9 + length data)%nat by lia.
  pose proof Nat.ceiling_add_le_mono (length msg + 9) 64 (length data).
  lia.
Qed.

Lemma padded_message_length msg :
  length (SHA256.padded_msg msg) = (padded_message_size msg / 4)%nat.
Proof.
  cbv [SHA256.padded_msg]. change (N.to_nat SHA256.w / 8)%nat with 4%nat.
  length_hammer.
Qed.
Hint Rewrite @padded_message_length : push_length.

(* Helper lemma for converting to words *)
Lemma padded_message_size_modulo4 msg :
  (padded_message_size msg mod 4 = 0)%nat.
Proof.
  pose proof padded_message_size_modulo msg.
  prove_by_zify.
Qed.

Lemma nth_padded_msg msg i :
  nth i (SHA256.padded_msg msg) 0%N
  = BigEndianBytes.concat_bytes
      [nth (i*4) (SHA256.padded_msg_bytes msg) x00
       ; nth (i*4 + 1) (SHA256.padded_msg_bytes msg) x00
       ; nth (i*4 + 2) (SHA256.padded_msg_bytes msg) x00
       ; nth (i*4 + 3) (SHA256.padded_msg_bytes msg) x00].
Proof.
  cbv [SHA256.padded_msg]. change (N.to_nat SHA256.w / 8)%nat with 4%nat.
  rewrite nth_bytes_to_Ns by (push_length; auto using padded_message_size_modulo4).
  cbn [List.map seq]. natsimpl. reflexivity.
Qed.

Lemma nth_padding_0 msg : nth 0 (SHA256.padding msg) x00 = x80.
Proof. reflexivity. Qed.
Hint Rewrite nth_padding_0 : push_nth.

Lemma padding_length msg :
  length (SHA256.padding msg) = (padded_message_size msg - length msg - 8)%nat.
Proof.
  rewrite <-padded_message_bytes_length.
  cbv [SHA256.padded_msg_bytes]. push_length.
  lia.
Qed.
Hint Rewrite @padding_length : push_length.

Lemma nth_padding_succ msg i :
  nth (S i) (SHA256.padding msg) x00 = x00.
Proof.
  destr (S i <? length (SHA256.padding msg))%nat;
    [ | apply nth_overflow; lia ].
  cbv [SHA256.padding] in *. autorewrite with push_length in *.
  push_nth. reflexivity.
Qed.
Hint Rewrite nth_padding_succ : push_nth.

Lemma nth_padding_nonzero msg i :
  (0 < i)%nat -> nth i (SHA256.padding msg) x00 = x00.
Proof.
  destruct i; [ lia | ]. intros.
  apply nth_padding_succ.
Qed.
