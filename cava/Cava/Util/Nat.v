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

  Lemma double_succ_double n : (N.double n + 1 = N.succ_double n)%N.
  Proof.
    rewrite !N.double_spec, !N.succ_double_spec. reflexivity.
  Qed.

  Lemma succ_double_succ n : (N.succ_double n + 1 = N.double (n + 1))%N.
  Proof.
    rewrite !N.double_spec, !N.succ_double_spec. lia.
  Qed.

  Lemma succ_double_double_neq n m : N.succ_double n <> N.double m.
  Proof.
    rewrite N.double_spec, N.succ_double_spec. nia.
  Qed.

  Lemma succ_double_testbit n i :
    N.testbit (N.succ_double n) i = if (i =? 0)%N then true else N.testbit n (i-1).
  Proof.
    destruct i; subst.
    { rewrite N.bit0_odd; apply Ndouble_plus_one_bit0. }
    { destruct n, p; try congruence; try reflexivity. }
  Qed.

  Lemma double_testbit n i :
    N.testbit (N.double n) i = if (i =? 0)%N then false else N.testbit n (i-1).
  Proof.
    destruct i; subst.
    { rewrite N.bit0_odd. apply Ndouble_bit0. }
    { destruct n, p; try congruence; try reflexivity. }
  Qed.

  Lemma mod_pow2_bits_full n m i :
    N.testbit (n mod 2 ^ m) i = if (i <? m)%N then N.testbit n i else false.
  Proof.
    case_eq (N.ltb i m); rewrite ?N.ltb_lt, ?N.ltb_ge; intros;
     rewrite ?N.mod_pow2_bits_low, ?N.mod_pow2_bits_high by lia;
      try reflexivity.
  Qed.

  Lemma div_mul_l a b : (b <> 0)%N -> ((b * a) / b)%N = a.
  Proof. intros; rewrite N.mul_comm. apply N.div_mul. auto. Qed.

  Lemma mod_mul_l a b : (b <> 0)%N -> ((b * a) mod b = 0)%N.
  Proof. intros; rewrite N.mul_comm. apply N.mod_mul. auto. Qed.

  Lemma succ_double_double n : (N.succ_double n- 1)%N = N.double n.
  Proof. destruct n; reflexivity. Qed.

  Lemma ones_succ sz : N.ones (N.of_nat (S sz)) = N.succ_double (N.ones (N.of_nat sz)).
  Proof.
    cbv [N.ones].
    rewrite !N.shiftl_1_l, !N.pred_sub, N.succ_double_spec.
    rewrite Nat2N.inj_succ, N.pow_succ_r by lia.
    assert (2 ^ N.of_nat sz <> 0)%N by (apply N.pow_nonzero; lia).
    lia.
  Qed.

End N.
Hint Rewrite N.clearbit_eq N.b2n_bit0 N.shiftr_spec'
     N.pow2_bits_true N.add_bit0 N.land_spec N.lor_spec
     N.testbit_even_0 N.setbit_eqb N.pow2_bits_eqb N.ldiff_spec
     N.div2_bits N.double_bits_succ N.clearbit_eqb
     N.bits_0 N.succ_double_testbit N.double_testbit
     N.mod_pow2_bits_full
     using solve [eauto] : push_Ntestbit.
