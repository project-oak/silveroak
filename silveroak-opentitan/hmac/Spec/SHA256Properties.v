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

Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.Tactics.
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
  end; subst W_formula; cbn beta; autorewrite with natsimpl push_nth;
    [ solve [auto] | ].
  destruct_one_match; autorewrite with push_nth; reflexivity.
Qed.

Lemma H0_length : length SHA256.H0 = 8%nat.
Proof. reflexivity. Qed.
Hint Rewrite @H0_length using solve [eauto] : push_length.

Lemma sha256_compress_length msg i H t :
  length (SHA256.sha256_compress msg i H t) = 8%nat.
Proof. reflexivity. Qed.
Hint Rewrite @sha256_compress_length using solve [eauto] : push_length.

Lemma fold_left_sha256_compress_length msg i H ts :
  length H = 8%nat ->
  length (fold_left (SHA256.sha256_compress msg i) ts H) = 8%nat.
Proof.
  intros. apply fold_left_invariant with (I:=fun H => length H = 8%nat); auto.
Qed.
Hint Rewrite @fold_left_sha256_compress_length using solve [length_hammer]
  : push_length.

Lemma sha256_step_length msg H i :
  length H = 8%nat -> length (SHA256.sha256_step msg H i) = 8%nat.
Proof. intros; cbv [SHA256.sha256_step]. length_hammer. Qed.
Hint Rewrite @sha256_step_length using solve [length_hammer] : push_length.

Lemma fold_left_sha256_step_length msg H idxs :
  length H = 8%nat -> length (fold_left (SHA256.sha256_step msg) idxs H) = 8%nat.
Proof.
  intros. apply fold_left_invariant with (I:=fun H => length H = 8%nat); auto.
  intros; length_hammer.
Qed.
Hint Rewrite @fold_left_sha256_step_length using solve [length_hammer]
  : push_length.
