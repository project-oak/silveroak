(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
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
Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.

(* Natural number simplifications are also useful for lists *)
Lemma sub_succ_l_same n : S n - n = 1.
Proof. lia. Qed.
Hint Rewrite Nat.add_0_l Nat.add_0_r Nat.sub_0_r Nat.sub_0_l Nat.sub_diag
     using solve [eauto] : natsimpl.
Hint Rewrite Nat.sub_succ sub_succ_l_same using solve [eauto] : natsimpl.
Hint Rewrite Min.min_r Min.min_l Nat.add_sub using lia : natsimpl.
Hint Rewrite (fun n m => proj2 (Nat.sub_0_le n m)) using lia : natsimpl.

Module Nat2N.
  Lemma inj_pow a n : (N.of_nat a ^ N.of_nat n)%N = N.of_nat (a ^ n).
  Proof.
    induction n; intros; [ reflexivity | ].
    rewrite Nat.pow_succ_r by Lia.lia.
    rewrite Nat2N.inj_succ, N.pow_succ_r by lia.
    rewrite IHn. lia.
  Qed.
End Nat2N.

Module Pos.
  Lemma size_nat_equiv (x : positive) :
    Pos.size_nat x = Pos.to_nat (Pos.size x).
  Proof.
    induction x; intros; cbn [Pos.size_nat Pos.size];
      rewrite ?Pnat.Pos2Nat.inj_succ; (reflexivity || congruence).
  Qed.
End Pos.

Module N.
  Lemma size_nat_equiv (x : N) :
    N.size_nat x = N.to_nat (N.size x).
  Proof.
    destruct x as [|p]; [ reflexivity | ].
    apply Pos.size_nat_equiv.
  Qed.

  Lemma size_nat_le (n : nat) (x : N) :
    (x < 2 ^ N.of_nat n)%N ->
    N.size_nat x <= n.
  Proof.
    destruct (N.eq_dec x 0);
      [ intros; subst; cbn [N.size_nat]; lia | ].
    destruct n; [ rewrite N.pow_0_r; lia | ].
    intros. rewrite size_nat_equiv, N.size_log2 by auto.
    pose proof (proj1 (N.log2_lt_pow2 x (N.of_nat (S n)) ltac:(lia))
                      ltac:(eassumption)).
    lia.
  Qed.

  Lemma size_nat_le_nat sz n : n < 2 ^ sz -> N.size_nat (N.of_nat n) <= sz.
  Proof.
    clear; intros. apply size_nat_le.
    change 2%N with (N.of_nat 2).
    rewrite Nat2N.inj_pow. lia.
  Qed.
End N.
