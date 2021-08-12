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
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.Sha256.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require HmacSpec.SHA256.
Import ListNotations.

(* TODO: move to a more general file *)
Lemma step_vec_as_tuple_cons {t n} x0 (xs : list (denote_type t)) :
  step (vec_as_tuple (t:=t) (n:=S n)) tt (x0 :: xs, tt)
  = (tt, (x0, snd (step (vec_as_tuple (t:=t) (n:=n)) tt (xs, tt)))).
Proof. reflexivity. Qed.
Hint Rewrite @step_vec_as_tuple_cons using solve [eauto] : stepsimpl.
Lemma step_vec_as_tuple_one {t} (x : denote_type t):
  step (vec_as_tuple (t:=t) (n:=0)) tt ([x], tt) = (tt, x).
Proof. reflexivity. Qed.
Hint Rewrite @step_vec_as_tuple_one using solve [eauto] : stepsimpl.
Ltac stepsimpl :=
  repeat first [ progress
                   cbn [fst snd step denote_type absorb_any
                            split_absorbed_denotation combine_absorbed_denotation
                            unary_semantics binary_semantics ]
               | progress autorewrite with stepsimpl ].

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
  length H = 8 ->
  k = nth t SHA256.K 0%N ->
  w = nth t (SHA256.W msg i) 0%N ->
  step sha256_compress tt (H,(k,(w,tt)))
  = (tt, SHA256.sha256_compress msg i H t).
Proof.
  intros. subst; destruct_lists_by_length.
  cbv [sha256_compress]. stepsimpl. reflexivity.
Qed.
Hint Rewrite @step_sha256_compress using solve [eauto] : stepsimpl.
