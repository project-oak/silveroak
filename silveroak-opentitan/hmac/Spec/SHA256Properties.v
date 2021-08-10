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
Require Import coqutil.Z.PushPullMod.
Require Import HmacSpec.SHA256.
Import ListNotations.
Local Open Scope N_scope.

(* k is a solution to the equation:
     l + 1 + k = 448 (mod 512) *)
Lemma k_correct l : (l + 1 + k l) mod 512 = 448.
Proof.
  cbv [k].
  lazymatch goal with |- context [Z.to_N (?a mod ?b)] =>
                      pose proof Z.mod_pos_bound a b ltac:(lia) end.
  rewrite <-(N2Z.id (l + 1)), <-Z2N.inj_add by lia.
  rewrite N2Z.inj_add. change (Z.of_N 1) with 1%Z.
  change 512 with (Z.to_N 512). change 448 with (Z.to_N 448).
  rewrite <-Z2N.inj_mod, Z.add_mod_idemp_r by lia.
  let x := lazymatch goal with |- Z.to_N (?x mod _)%Z = _ => x end in
  ring_simplify x. reflexivity.
Qed.

(* Prove that k < 512 *)
Lemma k_small l : k l < 512.
Proof.
  cbv [k]. change 512 with (Z.to_N 512).
  lazymatch goal with |- context [Z.to_N (?a mod ?b)] =>
                      pose proof Z.mod_pos_bound a b ltac:(lia) end.
  apply Z2N.inj_lt; [ lia .. | ].
  apply Z.mod_pos_bound. lia.
Qed.

(* Prove that k is the smallest non-negative solution to the equation *)
Lemma k_smallest l n : (l + 1 + n) mod 512 = 448 -> n >= k l.
Proof.
  intro Hn.
  assert (n mod 512 = k l mod 512) as Hmod_eq.
  { cbv [k].
    change 448%Z with (Z.of_N 448). rewrite <-Hn.
    change 512%N with (Z.to_N 512). rewrite <-(N2Z.id n).
    lazymatch goal with |- context [Z.to_N (?a mod ?b)] =>
                        pose proof Z.mod_pos_bound a b ltac:(lia) end.
    rewrite <-!Z2N.inj_mod by lia.
    apply Z2N.inj_iff; [ try apply Z.mod_pos_bound; lia .. | ].
    rewrite N2Z.inj_mod by lia. rewrite !N2Z.id, !Z2N.id by lia.
    rewrite !N2Z.inj_add. change (Z.of_N 1) with 1%Z.
    Z.push_mod. Z.pull_mod.
    (* TODO: why is this not in Z.pull_mod? *)
    rewrite !Zmod_mod. rewrite !Zminus_mod_idemp_r.
    rewrite !Zminus_mod_idemp_l.
    let x := lazymatch goal with |-_ = (?x mod _)%Z => x end in
    ring_simplify x. reflexivity. }
  rewrite (N.mod_small (k l)) in Hmod_eq by apply k_small.
  rewrite <-Hmod_eq.
  pose proof (N.mod_le n 512 ltac:(lia)). lia.
Qed.
