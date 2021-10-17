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
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.

Require Import coqutil.Tactics.Tactics.

Import ListNotations.

Local Open Scope N.

(* Convert the least significant 8 bits of a number to a byte *)
Definition N_to_byte (x : N) : byte :=
  match Byte.of_N (x mod 2^8) with
  | Some b => b
  | None => x00
  end.

Module BigEndianBytes.
  (* evaluate a big-endian list of bytes *)
  Definition concat_bytes (bs : list byte) : N :=
    List.fold_left (fun acc b => N.lor (N.shiftl acc 8) (Byte.to_N b)) bs 0%N.

  (* convert the least significant (n*8) bits of a number to big-endian bytes *)
  Definition N_to_bytes n (x : N) : list byte :=
    List.map (fun i => N_to_byte (N.shiftr x (N.of_nat (n-1-i)*8)))
             (seq 0 n).

  (* convert a big-endian list of bytes to a list of n-byte words (length of list
   must be a multiple of n) *)
  Definition bytes_to_Ns n (x : list byte) : list N :=
    List.map (fun i => concat_bytes (firstn n (skipn (n*i) x))) (seq 0 (length x / n)).
End BigEndianBytes.

Definition byte_xor (x y : byte) : byte := N_to_byte (N.lxor (Byte.to_N x) (Byte.to_N y)).

Module N2Byte.
  Lemma id (x: N) : ((Byte.to_N (N_to_byte x)) = x mod 256)%N.
  Proof.
    cbv [N_to_byte].
    destr (Byte.of_N (x mod 2 ^ 8)).
    { rewrite Byte.to_of_N with (x:=(x mod 2^8)%N) by apply E. reflexivity. }
    { rewrite (Byte.of_N_None_iff (x mod 2^8))%N in E. exfalso.
      pose (N.mod_upper_bound x (2^8))%N.
      assert (2 ^ 8 <> 0)%N by (cbn;lia).
      specialize (l H).
      replace 255%N with (N.pred 256)%N in E by lia.
      apply N.lt_pred_le in E.
      apply N.lt_le_pred in l.
      rewrite l in E.
      cbn in E.
      lia.
    }
  Qed.

End N2Byte.

Module Byte2N.
  Lemma id x: (N_to_byte (Byte.to_N x) = x )%N.
  Proof. destr x; now cbn. Qed.

  Lemma inj x y: (Byte.to_N x = Byte.to_N y -> x = y)%N.
  Proof.  intro H. rewrite <- (id x), <- (id y). now f_equal. Qed.
End Byte2N.

Lemma testbit_byte b n:
  (8 <= n) ->
  N.testbit (Byte.to_N b) n = false.
Proof.
  intros.
  intros.
  remember (Byte.to_N b) as b'.
  pose (Byte.to_N_bounded b).
  apply N.lt_succ_r in l.
  change (N.succ 255) with (2^8) in l.
  rewrite <- Heqb' in l.
  apply N.testbit_high.
  apply (N.lt_le_trans _ (2^8));
    [ lia | apply N.pow_le_mono_r; lia ].
Qed.

Lemma unfold_N_to_bytes_4 x: BigEndianBytes.N_to_bytes 4 x =
  [N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 0) * 8));
  N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 1) * 8));
  N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 2) * 8));
  N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 3) * 8))].
Proof.
  cbv [BigEndianBytes.N_to_bytes].
  now cbn [List.map seq].
Qed.

Lemma shiftr_byte b x: (8 <= x) ->
  N.shiftr (Byte.to_N b) x = 0.
Proof.
  intros.
  remember (Byte.to_N b) as b'.
  pose (Byte.to_N_bounded b).
  apply N.shiftr_eq_0.
  apply N.lt_succ_r in l.
  apply (N.lt_le_trans _ (N.log2 256)).
  {
    destr (0<?b').
    2:{ destr (b'=?0); try rewrite E0; cbn; lia. }
    apply N.log2_lt_pow2. { lia. }
    cbn. now rewrite Heqb'.
  }
  now cbn.
Qed.

Lemma N_to_bytes_length n x : length (BigEndianBytes.N_to_bytes n x) = n.
Proof. cbv [BigEndianBytes.N_to_bytes]. length_hammer. Qed.
Hint Rewrite @N_to_bytes_length : push_length.

Lemma bytes_to_Ns_length n bs:
  (length (BigEndianBytes.bytes_to_Ns n bs) = length bs / n)%nat.
Proof. cbv [BigEndianBytes.bytes_to_Ns]. length_hammer. Qed.
Hint Rewrite @bytes_to_Ns_length : push_length.

Lemma N_to_byte_to_N x : Byte.to_N (N_to_byte x) = (x mod 256)%N.
Proof.
  cbv [N_to_byte]. change (2 ^ 8)%N with 256%N.
  pose proof N.mod_bound_pos x 256 ltac:(lia) ltac:(lia).
  pose proof proj1 (Byte.of_N_None_iff (x mod 256)).
  apply Byte.to_of_N.
  destruct (Byte.of_N (x mod 256)); [ reflexivity | ].
  lazymatch goal with H : None = None -> _ |- _ =>
                      specialize (H ltac:(reflexivity)) end.
  lia.
Qed.

Lemma nth_bytes_to_Ns i n bs :
  (length bs mod n = 0)%nat ->
  (n <> 0)%nat ->
  List.nth i (BigEndianBytes.bytes_to_Ns n bs) 0%N
  = BigEndianBytes.concat_bytes
      (List.map
         (fun j => List.nth (i*n + j) bs Byte.x00)
         (seq 0 n)).
Proof.
  cbv [BigEndianBytes.bytes_to_Ns]. intros.
  destruct (Compare_dec.lt_dec i (length bs / n)).
  { erewrite map_nth_inbounds with (d2:=0%nat) by length_hammer.
    cbv [BigEndianBytes.concat_bytes]. f_equal; [ ].
    push_nth. natsimpl.
    erewrite firstn_map_nth with (d:=Byte.x00).
    { eapply List.map_ext_in; intros *.
      rewrite in_seq; natsimpl; intros.
      push_nth. f_equal; lia. }
    { push_length.
      Zify.zify.
      (* extra step because zify fails to zify Nat.modulo and Nat.div *)
      rewrite ?mod_Zmod, ?div_Zdiv in * by lia.
      Zify.zify; Z.to_euclidean_division_equations.
      (* N.B. this needs nia instead of lia *)
      nia. } }
  { push_nth. cbv [BigEndianBytes.concat_bytes].
    assert (length bs <= i * n)%nat.
    { Zify.zify.
      (* extra step because zify fails to zify Nat.modulo and Nat.div *)
      rewrite ?mod_Zmod, ?div_Zdiv in * by lia.
      Zify.zify; Z.to_euclidean_division_equations.
      (* N.B. this needs nia instead of lia *)
      nia. }
    apply fold_left_invariant with (I:= eq 0%N); [ reflexivity | | tauto ].
    intros *; rewrite in_map_iff.
    intros; logical_simplify; subst.
    match goal with H : _ |- _ => apply in_seq in H end.
    push_nth. reflexivity. }
Qed.

Lemma N_to_byte_equiv x y :
  (x mod 256 = y mod 256)%N -> N_to_byte x = N_to_byte y.
Proof.
  intro Heq. cbv [N_to_byte]. compute_expr (2 ^ 8)%N.
  rewrite Heq. reflexivity.
Qed.

Lemma nth_N_to_bytes i n x :
  (i < n)%nat ->
  List.nth i (BigEndianBytes.N_to_bytes n x) Byte.x00
  = N_to_byte (N.shiftr (N.land x (N.ones (8 * N.of_nat n)))
                        (N.of_nat (n - 1 - i) * 8)).
Proof.
  intros. cbv [BigEndianBytes.N_to_bytes].
  push_nth; natsimpl. apply N_to_byte_equiv.
  change 256%N with (2 ^ 8)%N.
  apply N.bits_inj; intro j.
  push_Ntestbit; boolsimpl.
  case_eq (j <? 8)%N; intros; N.bool_to_prop; [ | reflexivity ].
  push_Ntestbit. boolsimpl.
  f_equal; lia.
Qed.

Lemma concat_bytes_spec_low bs n:
  n < (N.of_nat (length bs) * 8) + 8->
  forall y,
  (forall n', n' < 8 -> N.testbit y n' = false) ->
  N.testbit
    (fold_left
    (fun (acc : N) (b : byte) => N.lor (N.shiftl acc 8) (Byte.to_N b)) bs y)
    n = N.testbit (Byte.to_N (nth (N.to_nat (n / 8)) (rev bs) "000"%byte)) (n mod 8).
Proof.
  revert n.

  replace bs with (rev (rev bs)) by apply rev_involutive.
  rename bs into x.
  remember (rev x) as bs; clear Heqbs x.
  rewrite rev_involutive.

  induction bs.
  { intros; cbn in *.
    destruct (N.to_nat (n / 8)); destr (n <? 8); try lia;
      rewrite N.mod_small by lia; rewrite H0 by lia; now push_Ntestbit.
  }
  intros.
  cbn [rev].
  rewrite fold_left_app.
  cbn [fold_left].
  destr (n <? 8); push_Ntestbit.
  { replace (n/8) with 0 by (rewrite N.div_small; lia).
    cbn.
    now rewrite N.mod_small by lia.
  }
  replace (n/8) with (1 + ((n - 8)/8)) .
  2:{ zify. Z.to_euclidean_division_equations. lia. }

  replace (N.to_nat (1 + (n - 8) / 8)) with (S (N.to_nat ((n - 8) / 8))) by lia.
  rewrite nth_step.

  replace (n mod 8) with ((n - 8) mod 8).
  2:{ zify. Z.to_euclidean_division_equations. lia. }

  rewrite testbit_byte by lia.
  boolsimpl.
  apply IHbs.
  { remember (n - 8) as n'.
    apply (N.add_cancel_r n' (n-8) 8) in Heqn'.
    rewrite N.sub_add in Heqn' by lia.
    rewrite <- Heqn' in H.
    rewrite rev_length in H.
    cbn [length] in H.
    apply N.add_lt_mono_r in H.
    push_length.
    replace (N.of_nat (length bs) * 8 + 8) with (N.of_nat (S (length bs)) * 8) by lia.
    apply H.
  }
  apply H0.
Qed.

Lemma concat_bytes_spec_high bs n:
  N.of_nat (length bs) * 8 + 8 <= n ->
  N.testbit (fold_left (fun (acc : N) (b : byte) => N.lor (N.shiftl acc 8) (Byte.to_N b)) bs 0) n =
  N.testbit (Byte.to_N (nth (N.to_nat (n / 8)) (rev bs) "000"%byte)) (n mod 8).
Proof.
  intros.
  revert n H.
  replace bs with (rev (rev bs)) by apply rev_involutive.
  rename bs into x.
  remember (rev x) as bs; clear Heqbs x.
  rewrite rev_involutive.
  induction bs.
  { intros. cbn. destruct (N.to_nat (n/8)); now cbn. }

  intros.
  cbn [rev].
  rewrite fold_left_app.
  cbn [fold_left].
  push_Ntestbit.

  replace (n/8) with (1 + ((n - 8)/8)).
  2:{ zify. Z.to_euclidean_division_equations. lia. }

  replace (N.to_nat (1 + (n - 8) / 8)) with (S (N.to_nat ((n - 8) / 8))) by lia.
  rewrite nth_step.

  replace (n mod 8) with ((n - 8) mod 8).
  2:{ zify. Z.to_euclidean_division_equations. lia. }

  rewrite testbit_byte by lia.
  boolsimpl.
  apply IHbs.
  replace (N.of_nat ( length (rev (a:: bs)))) with (1 + N.of_nat (length bs)) in H by (push_length;lia).
  rewrite N.mul_add_distr_r in H.
  rewrite <- N.add_assoc in H.
  apply N.le_add_le_sub_l in H.
  change (1*8) with 8 in H.
  push_length; apply H.
Qed.

Lemma concat_bytes_spec bs n:
  N.testbit (BigEndianBytes.concat_bytes bs) n =
  N.testbit (Byte.to_N (nth (N.to_nat (n / 8)) (rev bs) x00)) (n mod 8).
Proof.
  cbv [BigEndianBytes.concat_bytes].
  destr (n <? N.of_nat (length bs) * 8 + 8).
  {
    apply concat_bytes_spec_low.
    { apply E. }
    { intros. now push_Ntestbit. }
  }
  now apply concat_bytes_spec_high.
Qed.

Hint Rewrite @concat_bytes_spec : push_Ntestbit.

Lemma testbit_mod_idx n m x y:
  m <> 0 ->
  (forall n', n' < m -> N.testbit x n' = y)
  -> N.testbit x (n mod m) = y.
Proof.
  intros.

  rewrite N.mod_eq by lia.
  apply H0.
  zify. Z.to_euclidean_division_equations. lia.
Qed.

Lemma testbit_mod_same_idx n m o x y:
  o <> 0 ->
  (n mod o = m mod o) ->
  (forall n', n' < o -> N.testbit x n' = N.testbit y n')
  -> N.testbit x (n mod o) = N.testbit y (m mod o).
Proof.
  intros.
  do 2 rewrite N.mod_eq by lia.
  repeat rewrite N.mod_eq in H0 by lia.
  rewrite H0.
  apply H1.
  zify. Z.to_euclidean_division_equations. lia.
Qed.

Lemma concat_bytes_last_spec b bs n:
  n < 8 ->
  forall y,
  N.testbit
    (fold_left
    (fun (acc : N) (b : byte) => N.lor (N.shiftl acc 8) (Byte.to_N b)) (bs ++ [b]) y)
       n = N.testbit (Byte.to_N (nth (length bs  - N.to_nat (n / 8)) (bs ++ [b]) "000"%byte)) (n mod 8).
Proof.
  intros H.
  induction bs.

  { intros; cbn.
    rewrite N.mod_small by lia.
    push_Ntestbit.
    reflexivity.
  }

  { intros.
    rewrite <- app_comm_cons.
    rewrite fold_left_cons.
    push_length.
    replace (S (length bs) - N.to_nat (n / 8))%nat with (S (length bs - N.to_nat (n / 8)))%nat by
      now rewrite minus_Sn_m by (rewrite N.div_small; lia).

    rewrite nth_step.
    apply IHbs.
  }
Qed.

Lemma concat_bytes_skip_4_of_8_spec xs n:
    (length xs < 8)%nat ->
    n < 32 ->
      N.testbit
        (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 (skipn 4 xs))) n = false.
Proof.
  repeat (destruct xs; try cbn; try lia);
    intros; repeat rewrite N.lor_0_r; repeat rewrite N.shiftl_shiftl;
    now repeat (push_Ntestbit; boolsimpl).
Qed.

Lemma concat_bytes_lower_8_zero xs n:
    (length xs < 4)%nat ->
    n < 32 ->
      N.testbit
        (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 xs)) n = false.
Proof.
  repeat (destruct xs; try cbn; try lia);
    intros; repeat rewrite N.lor_0_r; repeat rewrite N.shiftl_shiftl;
    now repeat (push_Ntestbit; boolsimpl).
Qed.

Lemma concat_bytes_skip_lower32 xs n:
      32 <= n -> n < 64 ->
      N.testbit (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 xs)) (n - 32) =
      N.testbit (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 (skipn 4 xs))) n.
Proof.
  intros.
  push_Ntestbit.
  apply testbit_mod_same_idx; try lia.
  { zify; Z.to_euclidean_division_equations; lia. }
  intros.
  do 2 f_equal.
  do 2 rewrite rev_nth by
    ( push_length; zify; Z.to_euclidean_division_equations; lia).
  cbv [resize].
  push_length.
  destruct (Nat.ltb_spec
    (Init.Nat.min 8 (length xs) + (8 - length xs) - S (N.to_nat ((n - 32) / 8)))
    (Init.Nat.min 8 (length xs))).
  {
    assert
      (Init.Nat.min 8 (length xs - 4) + (8 - (length xs - 4)) - S (N.to_nat (n / 8))
      < Init.Nat.min 8 (length xs - 4))%nat.
    { zify; Z.to_euclidean_division_equations; lia. }
    repeat rewrite app_nth1 by (push_length; lia).
    repeat rewrite nth_firstn_inbounds by lia.
    rewrite nth_skipn.
    f_equal.
    { zify; Z.to_euclidean_division_equations; lia. }
  }
  assert
    (Init.Nat.min 8 (length xs - 4) + (8 - (length xs - 4)) - S (N.to_nat (n / 8))
    >= Init.Nat.min 8 (length xs - 4))%nat.
  { zify; Z.to_euclidean_division_equations; lia. }
  repeat rewrite app_nth2 by (push_length; lia).
  repeat rewrite nth_repeat.
  now repeat rewrite Tauto.if_same.
Qed.

Lemma concat_bytes_8_is_64bit xs n:
      64 <= n ->
      N.testbit
        (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 xs))
        n = false.
Proof.
  intros. push_Ntestbit.
  assert (8 <= n/8).
  { zify; Z.to_euclidean_division_equations; lia. }
  rewrite <- N2Nat.id with (a:=n/8).
  remember (N.to_nat (n/8)) as x.
  rewrite Nat2N.id.
  destr (x <? 8)%nat;[lia|].
  rewrite nth_overflow by (push_length; lia).
  now push_Ntestbit.
Qed.

Lemma concat_bytes_resize_masked x:
      N.shiftr
        (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 x))
        (N.of_nat 32) mod 2 ^ N.of_nat 32 =
      BigEndianBytes.concat_bytes (List.resize Byte.x00 4 x).
Proof.
  rewrite <- N.land_ones.
  apply N.bits_inj. intros n.
  destr (n <? 32).
  { push_Ntestbit; boolsimpl.
    apply testbit_mod_same_idx; try lia.
    { zify; Z.to_euclidean_division_equations; lia. }
    intros.
    replace ((n + N.of_nat 32) / 8) with ((n/8) + 4).
    2:{ zify; Z.to_euclidean_division_equations; lia. }
    rewrite <- N2Nat.id with (n/8) in *.
    remember (N.to_nat (n/8)) as j.
    rewrite Nat2N.id.
    assert(j < 4)%nat.
    { zify; Z.to_euclidean_division_equations; lia. }
    repeat rewrite rev_nth by (push_length; lia).
    replace (N.to_nat (N.of_nat j + 4)) with (j + 4)%nat by lia.
    push_length.
    f_equal.
    f_equal.
    cbv [resize].
    destruct (Nat.ltb_spec (8 - S (j + 4)) (Init.Nat.min 8 (length x))).
    {
      assert (4 - S j < Init.Nat.min 4 (length x))%nat by lia.
      repeat rewrite app_nth1 by (push_length; lia).
      repeat rewrite nth_firstn_inbounds by lia.
      f_equal.
      lia.
    }
    {
      assert (Init.Nat.min 4 (length x) <= 4 - S j)%nat by lia.
      repeat rewrite app_nth2 by (push_length; lia).
      repeat rewrite nth_repeat.
      now repeat rewrite Tauto.if_same.
    }
  }
  push_Ntestbit;boolsimpl.
  rewrite nth_overflow.
  { now push_Ntestbit. }
  push_length.
  { zify; Z.to_euclidean_division_equations; lia. }
Qed.

Lemma bytes_to_N_id_4 xs:
  length xs = 4%nat ->
  BigEndianBytes.N_to_bytes 4 (BigEndianBytes.concat_bytes xs) = xs.
Proof.
  intros.
  rewrite unfold_N_to_bytes_4.
  do 5 (destruct xs; try (cbn in *; lia)).
  cbn [BigEndianBytes.concat_bytes fold_left Nat.sub Nat.mul].
  do 4 f_equal.
  all:
    apply Byte2N.inj; rewrite N2Byte.id; change 256 with (2^8);
    rewrite <- N.land_ones;
    apply N.bits_inj; intro x; push_Ntestbit; boolsimpl;
    destruct (N.ltb_spec x 8);
    push_Ntestbit; boolsimpl;
      repeat rewrite testbit_byte by lia; [
      repeat rewrite <- N.add_sub_assoc by lia;
      cbn;
      rewrite N.add_0_r;
      repeat match goal with | |- context [N.testbit ?b ?N] => rewrite testbit_byte with (n:=N) by (cbn; lia) end;
      now boolsimpl
    | reflexivity].
Qed.

Local Ltac tb A :=
  rewrite <- Byte2N.id with (x:=A);
  remember (Byte.to_N A).

Lemma concat_bytes_4_bound xs:
  BigEndianBytes.concat_bytes (List.resize Byte.x00 4 xs) < 2 ^ 32.
Proof.
  assert (exists a b c d, [a;b;c;d] = resize Byte.x00 4 xs).
  { do 4 (destruct xs; [repeat eexists|]).
    repeat eexists.
  }
  logical_simplify.
  rewrite <- H.
  cbn.
  repeat rewrite N.shiftl_mul_pow2.
  tb x; tb x0; tb x1; tb x2.
  repeat rewrite N2Byte.id.
  repeat rewrite N.lor_high_low_add.
  cbn. zify. Z.to_euclidean_division_equations. lia.
Qed.

Lemma concat_bytes_8_bound xs:
  BigEndianBytes.concat_bytes (List.resize Byte.x00 8 xs) < 2 ^ 64.
Proof.
  assert (exists a b c d e f g h, [a;b;c;d;e;f;g;h] = resize Byte.x00 8 xs).
  { do 8 (destruct xs; [repeat eexists|]).
    repeat eexists.
  }
  logical_simplify.
  rewrite <- H.
  cbn.
  repeat rewrite N.shiftl_mul_pow2.
  tb x; tb x0; tb x1; tb x2; tb x3; tb x4; tb x5; tb x6.
  repeat rewrite N2Byte.id.
  repeat rewrite N.lor_high_low_add.
  cbn. zify. Z.to_euclidean_division_equations. lia.
Qed.

Lemma concat_bytes_truncation x:
  (N.shiftr
    (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 x))
    (N.of_nat 32) mod 2 ^ N.of_nat 32)%N
    = BigEndianBytes.concat_bytes (List.resize Byte.x00 4 x).
Proof.
  change (N.of_nat 32) with 32.
  rewrite <- N.mod_small with (a:=BigEndianBytes.concat_bytes (resize "000"%byte 4 x)) (b:=2^32)
    by apply concat_bytes_4_bound.

  assert (exists a b c d e f g h, [a;b;c;d;e;f;g;h] = resize Byte.x00 8 x).
  { do 8 (destruct x; [repeat eexists|]).
    repeat eexists.
  }
  logical_simplify.
  rewrite <- H.
  assert ([x0;x1;x2;x3] = resize Byte.x00 4 x).
  {
    rewrite <- resize_resize with (m:=8%nat) by lia.
    rewrite <- H.
    now cbn.
  }
  rewrite <- H0.

  apply N.bits_inj; intro n;push_Ntestbit.
  destruct (N.ltb_spec n 32); [|reflexivity].
  apply testbit_mod_same_idx; try lia.
  { zify. Z.to_euclidean_division_equations. lia. }
  intros.
  cbn.
  replace (N.to_nat ((n+32)/8)) with (N.to_nat (n/8)%N + 4)%nat; cycle 1.
  { zify. Z.to_euclidean_division_equations. lia. }
  remember (N.to_nat (n/8)) as n0.
  destruct n0; cbn; [reflexivity|].
  destruct n0; cbn; [reflexivity|].
  destruct n0; cbn; [reflexivity|].
  destruct n0; cbn; [reflexivity|].
  { zify. Z.to_euclidean_division_equations. lia. }
Qed.


Local Ltac testbit_crush :=
  repeat lazymatch goal with
         | |- context [N.eqb ?x ?y] => destr (N.eqb x y); try lia; subst
         | |- N.testbit ?x _ = N.testbit ?x _ => f_equal; lia
         | H: (?X < ?Y)%N |- context [if (?X <? ?Y)%N then _ else _] =>
           rewrite (proj2 (N.ltb_lt X Y) H)
         | _ => first [ progress (push_Ntestbit; boolsimpl) | reflexivity ]
         end.
