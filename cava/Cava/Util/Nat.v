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
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import coqutil.Tactics.Tactics.

Lemma sub_succ_l_same n : S n - n = 1.
Proof. lia. Qed.

(* Note: Do NOT add anything that produces side conditions; this causes problems
   because of a bug in autorewrite that means it doesn't backtrack if it fails
   to solve a side condition (see https://github.com/coq/coq/issues/7672) *)
Hint Rewrite Nat.add_0_l Nat.add_0_r Nat.sub_0_r Nat.sub_0_l
     Nat.sub_diag Nat.sub_succ sub_succ_l_same : natsimpl.
Hint Rewrite Nat.mul_0_l Nat.mul_0_r Nat.mul_1_l Nat.mul_1_r : natsimpl.
Hint Rewrite Nat.div_1_r : natsimpl.
Hint Rewrite Nat.mod_1_r : natsimpl.
Ltac natsimpl_step :=
  first [ progress autorewrite with natsimpl
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

Ltac natsimpl := repeat natsimpl_step.

(* convert to Z and use Z.to_euclidean_division_equations, then solve with
   [solver] *)
Ltac prove_by_zify' solver :=
  Zify.zify;
  (* extra step because zify fails to zify Nat.modulo and Nat.div *)
  repeat (progress rewrite ?mod_Zmod, ?div_Zdiv in * by lia;
          Zify.zify);
  Z.to_euclidean_division_equations; solver.
Ltac prove_by_zify := prove_by_zify' lia.

Module Nat.
  Lemma mul_div_exact_r a b :
    b <> 0 -> a mod b = 0 ->  a / b * b = a.
  Proof. intros. prove_by_zify. Qed.

  Lemma add_sub_cancel a b : a + b - a = b.
  Proof. lia. Qed.

  Definition ceiling (a b : nat) :=
    (a + b - 1) / b.

  Lemma ceiling_add_le_mono a b c :
    Nat.ceiling a b <= Nat.ceiling (a + c) b.
  Proof.
    cbv [Nat.ceiling]. destruct (Nat.eq_dec b 0); [ subst; reflexivity | ].
    prove_by_zify' nia.
  Qed.

  Lemma ceiling_equiv a b :
    Nat.ceiling a b = a / b + if a mod b =? 0 then 0 else 1.
  Proof.
    cbv [Nat.ceiling]. destruct (Nat.eq_dec b 0); [ subst; reflexivity | ].
    destruct (Nat.eq_dec (a mod b) 0).
    { rewrite (proj2 (Nat.eqb_eq _ _)) by lia.
      rewrite (Nat.div_mod a b) by lia. replace (a mod b) with 0 by lia.
      natsimpl. rewrite <-Nat.add_sub_assoc by lia.
      rewrite !(Nat.mul_comm b), Nat.div_mul, Nat.div_add_l by lia.
      rewrite (Nat.div_small (b - 1)) by lia.
      lia. }
    { rewrite (proj2 (Nat.eqb_neq _ _)) by lia.
      pose proof Nat.mod_bound_pos a b ltac:(lia) ltac:(lia).
      rewrite (Nat.div_mod a b) by lia.
      replace (b * (a / b) + a mod b + b - 1) with
          ((a / b + 1) * b + (a mod b - 1)) by lia.
      rewrite (Nat.mul_comm b (a / b)).
      rewrite !Nat.div_add_l by lia.
      rewrite (Nat.div_small (a mod b - 1)) by lia.
      rewrite (Nat.div_small (a mod b)) by lia.
      lia. }
  Qed.

  Lemma ceiling_add_same a b c :
    1 < c < b - 1 -> a mod b <= b - c ->
    Nat.ceiling (a + c) b = Nat.ceiling (a + 1) b.
  Proof.
    cbv [Nat.ceiling]. intros.
    destruct (Nat.eq_dec b 0); [ subst; reflexivity | ].
    rewrite (Nat.div_mod a b) by lia.
    replace (b * (a / b) + a mod b + c + b - 1) with
        ((a / b + 1) * b + (a mod b + c - 1)) by lia.
    replace (b * (a / b) + a mod b + 1 + b - 1) with
        ((a / b + 1) * b + a mod b) by lia.
    rewrite !Nat.div_add_l by lia.
    f_equal; [ ].
    rewrite !Nat.div_small; lia.
  Qed.

  Lemma ceiling_add_diff a b c :
    0 < b -> 0 < c < b -> b - c < a mod b ->
    Nat.ceiling (a + c) b = Nat.ceiling a b + 1.
  Proof.
    intros; rewrite !ceiling_equiv.
    destruct (Nat.eq_dec (a mod b) 0);
      [ rewrite (proj2 (Nat.eqb_eq _ _)) by lia
      | rewrite (proj2 (Nat.eqb_neq (a mod b) _)) by lia ].
    all:(destruct (Nat.eq_dec ((a + c) mod b) 0);
         [ rewrite (proj2 (Nat.eqb_eq _ _)) by lia
         | rewrite (proj2 (Nat.eqb_neq _ _)) by lia ]).
    all:prove_by_zify' nia.
  Qed.

  Lemma ceiling_range a b :
    0 < b -> 0 < a ->
    Nat.ceiling a b * b - b < a <= Nat.ceiling a b * b.
  Proof. cbv [Nat.ceiling]. intros. prove_by_zify. Qed.

  Lemma sub_mod_no_underflow x y :
    x < 2 ^ y -> 0 < x ->
    ((x + 2 ^ y - 1) mod 2 ^ y) = (x - 1).
  Proof.
    intros.
    rewrite Nat.add_sub_swap by trivial.
    rewrite Nat.add_mod by lia.
    rewrite Nat.mod_same by (try apply Nat.pow_nonzero; lia).
    rewrite Nat.add_0_r.
    rewrite Nat.mod_mod by lia.
    rewrite Nat.mod_small; lia.
  Qed.
End Nat.
Hint Rewrite Nat.add_sub_cancel : natsimpl.

Module Nat2N.
  Lemma inj_pow a n : (N.of_nat a ^ N.of_nat n)%N = N.of_nat (a ^ n).
  Proof.
    induction n; intros; [ reflexivity | ].
    rewrite Nat.pow_succ_r by Lia.lia.
    rewrite Nat2N.inj_succ, N.pow_succ_r by lia.
    rewrite IHn. lia.
  Qed.

  Lemma of_nat_if (b : bool) (x y: nat):
    N.of_nat (if b then x else y) = if b then N.of_nat x else N.of_nat y.
  Proof. now destruct b. Qed.
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

  Lemma mod_mod_mul_l a b c : b <> 0%N -> c <> 0%N -> ((a mod (b * c)) mod c = a mod c)%N.
  Proof.
    intros. rewrite (N.mul_comm b c).
    rewrite N.mod_mul_r, N.add_mod, N.mod_mul_l, N.add_0_r by lia.
    rewrite !N.mod_mod by lia. reflexivity.
  Qed.

  Lemma div_floor a b : b <> 0%N -> ((a - a mod b) / b = a / b)%N.
  Proof.
    intros. rewrite (N.div_mod a b) at 1 by lia.
    rewrite N.add_sub, N.div_mul_l; lia.
  Qed.

  Lemma mod_mul_div_r a b c :
    b <> 0%N -> c <> 0%N -> (a mod (b * c) / c = (a / c) mod b)%N.
  Proof.
    intros.
    rewrite (N.mul_comm b c), N.mod_mul_r by lia.
    rewrite (N.mul_comm c (_ mod b)), N.div_add by lia.
    rewrite (N.div_small (_ mod c) c) by (apply N.mod_bound_pos; lia).
    lia.
  Qed.

  Lemma lor_high_low_add a b c :
    N.lor (a * 2 ^ b) (c mod 2 ^ b) = (a * 2 ^ b + c mod 2 ^ b)%N.
  Proof.
    rewrite <-!N.shiftl_mul_pow2, <-!N.land_ones.
    apply N.bits_inj; intro i.
    rewrite !N.lor_spec, !N.land_spec.
    pose proof N.mod_pow2_bits_full (a * 2 ^ b + c mod 2 ^ b) b i as Hlow.
    rewrite N.add_mod, N.mod_mul, N.add_0_l, !N.mod_mod in Hlow
      by (apply N.pow_nonzero; lia).
    rewrite <-!N.shiftl_mul_pow2, <-!N.land_ones in Hlow.
    (* helpful assertion *)
    assert (2 ^ b <> 0)%N by (apply N.pow_nonzero; lia).
    destruct (i <? b)%N eqn:Hi;
      [ rewrite N.ltb_lt in Hi | rewrite N.ltb_ge in Hi ].
    { rewrite <-Hlow. rewrite !N.land_spec.
      rewrite N.shiftl_spec_low by lia.
      cbn [orb]. reflexivity. }
    { rewrite !N.land_spec in Hlow. rewrite Hlow.
      rewrite N.shiftl_spec_high by lia.
      rewrite Bool.orb_false_r.
      replace i with (i - b + b)%N by lia.
      rewrite N.add_sub. rewrite <-N.div_pow2_bits.
      rewrite N.shiftl_mul_pow2, N.land_ones.
      rewrite N.div_add_l by lia.
      rewrite N.div_small by (apply N.mod_bound_pos; lia).
      f_equal; lia. }
  Qed.

  Lemma testbit_high x n : (x < 2 ^ n)%N -> N.testbit x n = false.
  Proof.
    intros. destruct (N.eq_dec x 0%N); subst; [ reflexivity | ].
    apply N.bits_above_log2. apply N.log2_lt_pow2; lia.
  Qed.

  Lemma lor_lt x y xs ys: (x < 2 ^ xs -> y < 2^ys -> N.lor x y < N.max (2^xs) (2^ys))%N.
  Proof.
    intros.
    destr (xs <? ys)%N.
    {
      rewrite <- N.mod_small with (a:=y) (b:=(2^ys)%N) by lia.
      rewrite <- N.mod_small with (a:=x) (b:=(2^ys)%N) by
          (apply (N.lt_trans _ (2^xs));
            [|apply N.pow_lt_mono_r]; lia).

      rewrite <- N.land_ones.
      rewrite <- N.land_ones.

      rewrite <- N.land_lor_distr_l.
      rewrite N.land_ones.
      rewrite N.max_r by (apply N.pow_le_mono_r; lia).
      apply N.mod_upper_bound.
      lia.
    }

    {
      rewrite <- N.mod_small with (a:=x) (b:=(2^xs)%N) by lia.
      rewrite <- N.mod_small with (a:=y) (b:=(2^xs)%N) by
          (apply (N.lt_le_trans _ (2^ys));
            [|apply N.pow_le_mono_r]; lia).

      rewrite <- N.land_ones.
      rewrite <- N.land_ones.

      rewrite <- N.land_lor_distr_l.
      rewrite N.land_ones.
      rewrite N.max_l by (apply N.pow_le_mono_r; lia).
      apply N.mod_upper_bound.
      lia.
    }
  Qed.

  Lemma testbit_high_lt x n a: (x < 2 ^ n -> n <= a -> N.testbit x a = false)%N.
  Proof.
    intros.
    apply testbit_high.
    apply (N.lt_le_trans _ (2^n));
      [ lia | apply N.pow_le_mono_r; lia ].
  Qed.

  Lemma mod_mod_smaller: forall a n m: N, (((a mod 2 ^ n) mod 2 ^ m = a mod 2 ^ (N.min n m)))%N.
  Proof.
    intros.
    clear. intros.
    apply N.bits_inj.
    cbv [N.eqf]; intros x.

    destr (x <? m)%N;
    destr (x <? n)%N;
    destr (n <? m)%N;
    try rewrite N.min_l by lia;
    try rewrite N.min_r by lia;
    repeat rewrite N.mod_pow2_bits_low by easy;
    repeat rewrite N.mod_pow2_bits_high by easy;
    try reflexivity.

    { pose (N.lt_trans _ _ _ E0 E1). lia. }
  Qed.

  (* tactic for transforming boolean expressions about N arithmetic into Props *)
  Ltac bool_to_prop :=
    repeat lazymatch goal with
           | H : (_ =? _)%N = true |- _ => rewrite N.eqb_eq in H
           | H : (_ =? _)%N = false |- _ => rewrite N.eqb_neq in H
           | H : (_ <=? _)%N = true |- _ => rewrite N.leb_le in H
           | H : (_ <=? _)%N = false |- _ => rewrite N.leb_gt in H
           | H : (_ <? _)%N = true |- _ => rewrite N.ltb_lt in H
           | H : (_ <? _)%N = false |- _ => rewrite N.ltb_ge in H
           end.
End N.

(* Note: Do NOT add anything that produces side conditions; this causes problems
   because of a bug in autorewrite that means it doesn't backtrack if it fails
   to solve a side condition (see https://github.com/coq/coq/issues/7672) *)
Hint Rewrite N.clearbit_eq N.b2n_bit0 N.shiftr_spec'
     N.pow2_bits_true N.add_bit0 N.land_spec N.lor_spec
     N.testbit_even_0 N.setbit_eqb N.pow2_bits_eqb N.ldiff_spec
     N.div2_bits N.double_bits_succ N.clearbit_eqb
     N.bits_0 N.succ_double_testbit N.double_testbit
     N.mod_pow2_bits_full : push_Ntestbit.

Ltac push_Ntestbit_step :=
  match goal with
  | _ => progress autorewrite with push_Ntestbit
  | |- context [N.testbit (N.ones ?n) ?m]  =>
    first [ rewrite (N.ones_spec_high n m) by lia
          | rewrite (N.ones_spec_low n m) by lia ]
  | |- context [N.testbit (N.shiftl ?a ?n) ?m] =>
    first [ rewrite (N.shiftl_spec_high' a n m) by lia
          | rewrite (N.shiftl_spec_low a n m) by lia ]
  | |- context [N.testbit (N.lnot ?a ?n) ?m] =>
    first [ rewrite (N.lnot_spec_high a n m) by lia
          | rewrite (N.lnot_spec_low a n m) by lia ]
  | |- context [N.testbit ?x ?m] =>
    rewrite (N.testbit_high x m) by lia
  end.
Ltac push_Ntestbit := repeat push_Ntestbit_step.

Lemma le_1_is_0 x: (1 <=? x)%nat = negb (x =? 0)%nat.
Proof. destruct x; reflexivity. Qed.

Module N2Nat.
  (* TODO: these exists in latest Coq *)
  Lemma inj_mod a a' :
    N.to_nat (a mod a') = N.to_nat a mod N.to_nat a'.
  Proof. Admitted.
  Lemma inj_pow a a' :
    N.to_nat (a ^ a')%N = (N.to_nat a ^ N.to_nat a')%nat.
  Proof. Admitted.

  Lemma inj_leb x y: (x <=? y)%N = (N.to_nat x <=? N.to_nat y)%nat.
  Proof. Admitted.

  Lemma inj_ltb x y: (x <? y)%N = (N.to_nat x <? N.to_nat y)%nat.
  Proof. Admitted.

  Lemma inj_eqb x y: (x =? y)%N = (N.to_nat x =? N.to_nat y)%nat.
  Proof. Admitted.

  (* Get nice constants *)
  Lemma inj_0: N.to_nat 0 = 0. trivial. Qed.
  Lemma inj_1: N.to_nat 1 = 1. trivial. Qed.
  Lemma inj_2: N.to_nat 2 = 2. trivial. Qed.
  Lemma inj_3: N.to_nat 3 = 3. trivial. Qed.
End N2Nat.

Hint Rewrite
  N2Nat.inj_eqb N2Nat.inj_ltb N2Nat.inj_leb N2Nat.inj_mod N2Nat.inj_pow
  N2Nat.inj_0 N2Nat.inj_1 N2Nat.inj_2 N2Nat.inj_3
  : Nnat.

