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
Require Import Coq.Lists.List.

Require Import coqutil.Tactics.Tactics.

Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Byte.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.If.

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.Fifo.

Import ListNotations.

Local Open Scope bool.
Local Open Scope nat.
Local Open Scope list.

Lemma nz_s_1_a_1: forall x:nat, (x <> 0 -> x - 1 + 1 = x)%nat.
Proof. lia. Qed.

Lemma lt_nat_log2_simpl: forall x y,
  (y < 2 ^ (Nat.log2_up x ))%nat ->
  (N.of_nat y < 2 ^ N.of_nat (Nat.log2_up x))%N.
Proof.
  intros.
  change 2%N with (N.of_nat (S (S 0))).
  rewrite Nat2N.inj_pow.
  lia.
Qed.

Lemma inj_le: forall x, (1 <=? x)%N = negb (N.to_nat x =? 0)%nat.
Proof.
  intros.
  rewrite <- (N2Nat.id x).
  rewrite (Nat2N.id (N.to_nat x)).
  destruct (N.to_nat x); cbn.
  { reflexivity. }
  rewrite N.leb_le.
  lia.
Qed.

Lemma eqb_inj: forall x y, ( N.of_nat x =? N.of_nat y )%N = ( x =? y ).
Proof. intros.
  destruct (Nat.eqb_spec x y ).
  { rewrite e. rewrite N.eqb_refl. reflexivity. }
  { rewrite N.eqb_neq. lia. }
Qed.

Section FifoSpec.
  Context (T: type).
  Context (fifo_size: nat).
  Context (Hfifo_nz: (1 < fifo_size)%nat).

  Definition fifo_bits_size := Nat.log2_up (fifo_size + 1).

  Definition fifo_pre
    (contents: list (denote_type T))
    (input : denote_type (input_of (fifo (T:=T) fifo_size)))
    (state: denote_type (state_of (fifo (T:=T) fifo_size)))
    :=
    let '(valid, (data, (accepted_output,_))) := input in
    let '(_, (_, (fifo, count))) := state in
    (* if count is fifo_size we are full and we shouldn't be receiving  *)
    (if valid then N.to_nat count < fifo_size else True).

  Definition fifo_invariant
    (contents: list (denote_type T))
    (state: denote_type (state_of (fifo (T:=T) fifo_size)))
    :=
    let '(_, (_, (fifo, count))) := state in
    fifo_size = length fifo
    /\ N.to_nat count <= fifo_size
    /\ N.to_nat count = length contents
    /\ contents = rev (firstn (length contents) fifo)
  .

  Definition fifo_contents_update (empty full: bool) contents
      (input : denote_type (input_of (fifo (T:=T) fifo_size)))
      :=
    let '(valid, (data, (accepted_output,_))) := input in
    let contents' := if accepted_output && negb empty then tl contents else contents in
    contents' ++ if valid && negb full then [data] else [].

  Ltac N2nat_lt_2lg_solve x :=
    apply lt_nat_log2_simpl;
    apply (Nat.lt_le_trans _ (length x + 1)); [lia|];
    apply Nat.log2_up_spec; lia.

  (* Reduces the mod equations that arise here that aren't solved by e.g.
     Z.to_euclidean_division_equations, likely due to the non-constants modulus *)
  Local Ltac reduce_mod_eqs fifo contents :=
      match goal with
      | |- context [ N.modulo ?X ?Y ] =>
        let H := fresh in
        assert (X mod Y = X)%N as H;
        [ apply N.mod_small;
          N2nat_lt_2lg_solve fifo
        |]; rewrite H; clear H
      | |- context [ N.modulo ( ?X + ?Y - 1 ) ?Y ] =>
        let H := fresh in
        assert (( X + Y - 1 ) mod Y = X - 1)%N as H;
        let H1 := fresh in
        assert (forall x, 0 < x -> x <> 0)%N as H1 by lia;
        let H2 := fresh in
        assert (2 ^ N.of_nat (Nat.log2_up (Datatypes.length fifo + 1)) <> 0)%N as H2 by
          (
            apply H1;
            change 0%N with (N.of_nat 0)%nat;
            N2nat_lt_2lg_solve fifo
          );

        rewrite N.add_sub_swap by lia;
        rewrite <- N.add_mod_idemp_r by apply H2;

        rewrite N.mod_same by apply H2;
        rewrite N.add_0_r;

        rewrite N.mod_small;

        replace (N.of_nat (length contents) - 1)%N with (N.of_nat (length contents - 1))%N
          by apply Nat2N.inj_sub;

        [| N2nat_lt_2lg_solve fifo]

      | |- context [ N.modulo ( ?X + 1 ) ?Y ] =>
        let H := fresh in
        assert ( (X + 1)  mod Y = (X + 1) )%N as H;
        [ replace (N.of_nat( length contents ) + 1)%N with (N.of_nat (length contents  + 1)) by lia;
          apply N.mod_small;
          N2nat_lt_2lg_solve fifo
        |] ; rewrite H; clear H
      end.

  Lemma step_fifo_invariant
      contents new_contents
      (input : denote_type (input_of (fifo (T:=T) fifo_size)))
      (state : denote_type (state_of (fifo (T:=T) fifo_size))) :
    new_contents = fifo_contents_update (length contents =? 0) (length contents =? fifo_size) contents input ->
    fifo_pre contents input state ->
    fifo_invariant contents state ->
    fifo_invariant new_contents (fst (step (fifo fifo_size) state input)).
  Proof.
    destruct input as (input_valid, (input_data, (accepted_output, []))).
    destruct state as (s_valid, (s_data, (fifo, count))).
    intros Hcontents Hpre Hinv.
    destruct Hinv as [Hfifo_len [Hcount_bound [Hcontents_len Hcontents_rev_fifo ]]].
    cbv [fifo_pre fifo_invariant fifo_contents_update] in *.
    cbn in fifo.

    split.
    { destruct input_valid; stepsimpl; try rewrite length_removelast_cons; apply Hfifo_len. }

    (* *)
    assert (fifo <> []) as Hfifon_empty by
      (apply length_pos_nonnil; setoid_rewrite <- Hfifo_len; lia).

    stepsimpl.

    fold denote_type in *. (* denote_type is previously unfolded in some implicits *)

    rewrite inj_le.
    rewrite Hcontents_len.
    rewrite <- Nat2N.id in Hcontents_len.
    apply N2Nat.inj in Hcontents_len.
    subst.

    destruct (Nat.eqb_spec (@Datatypes.length (denote_type T) contents) 0)
      as [Hcontents_len_z | Hcontents_len_nz];
      destruct input_valid, accepted_output;
      stepsimpl;
      boolsimpl.

    (* Clean up terms *)
    all:
      try rewrite app_nil_r;
      try rewrite Hcontents_len_z;
      try change (N.of_nat 0 + 1)%N with (N.of_nat 1)%N;
      try replace (N.of_nat (length contents) + 1)%N with (N.of_nat (length contents + 1))%N by
        apply Nat2N.inj_add;
      try rewrite Nat2N.id.

    (* Simplify mod equations *)
    all: try reduce_mod_eqs fifo contents.

    all:
      try apply length_zero_iff_nil in Hcontents_len_z;
      try rewrite Nat2N.id in *;
      repeat ssplit.
    all: try (tauto || lia).

    all: subst; try rewrite app_nil_l.

    all: try (destruct fifo; tauto).

    5: {
      rewrite tl_length.
      lia.
    }
    5: {
      rewrite Hcontents_rev_fifo at 1.
      rewrite tl_rev.
      replace (length contents) with (S (length contents - 1)) by lia.
      rewrite removelast_firstn by lia.
      rewrite tl_length.
      reflexivity.
    }

    all:
      assert (Datatypes.length (contents) <> Datatypes.length fifo) by lia;
      destruct (Nat.eqb_spec (Datatypes.length (contents)) (Datatypes.length fifo)); try tauto;
      try rewrite app_length;
      try rewrite tl_length;
      try now (cbn; lia).

    all:
      rewrite Hcontents_rev_fifo at 1;
      try rewrite tl_rev;
      try (
        replace (length contents) with (S (length contents - 1)) by lia;
        rewrite removelast_firstn by lia);
      boolsimpl.

    {
      rewrite removelast_cons1 by tauto.
      cbn [length].
      rewrite nz_s_1_a_1 by lia.
      rewrite firstn_cons.
      cbn.
      rewrite firstn_removelast by lia.
      reflexivity.
    }

    {
      rewrite removelast_cons1 by tauto.
      cbn [length].
      rewrite Nat.add_1_r.
      rewrite firstn_cons.
      cbn.
      rewrite firstn_removelast by lia.
      reflexivity.
    }
  Qed.

  Definition fifo_spec
      (contents: list (denote_type T))
      (new_contents: list (denote_type T))
      (input : denote_type (input_of (fifo (T:=T) fifo_size)))
      (state : denote_type (state_of (fifo (T:=T) fifo_size)))
      : denote_type (Bit ** T ** Bit ** Bit) :=
    (negb (0 =? length contents)
    , (if 0 =? length contents then default else hd default contents
    , (length new_contents =? 0
    , length new_contents =? fifo_size)))%nat.

  Lemma step_fifo
      contents new_contents
      (input : denote_type (input_of (fifo (T:=T) fifo_size)))
      (state : denote_type (state_of (fifo (T:=T) fifo_size))) :
    new_contents = fifo_contents_update (length contents =? 0) (length contents =? fifo_size) contents input ->
    fifo_pre contents input state ->
    fifo_invariant contents state ->
    snd (step (fifo fifo_size) state input) = fifo_spec contents new_contents input state.
  Proof.
    destruct input as (input_valid, (input_data, (accepted_output, []))).
    destruct state as (s_valid, (s_data, (fifo, count))).
    intros Hcontents Hpre Hinv.
    destruct Hinv as [Hfifo_len [Hcount_bound [Hcontents_len Hcontents_rev_fifo]]].
    cbv [Fifo.fifo fifo_spec fifo_pre fifo_invariant fifo_contents_update K] in *.
    cbn in fifo.

    (* *)
    assert (fifo <> []) as Hfifon_empty by
      (apply length_pos_nonnil; setoid_rewrite <- Hfifo_len; lia).

    stepsimpl.
    repeat (destruct_pair_let; cbn [fst snd]).

    fold denote_type in *. (* denote_type is previously unfolded in some implicits *)

    logical_simplify.

    fold denote_type in *.

    rewrite inj_le.
    rewrite Hcontents_len.
    rewrite <- Nat2N.id in Hcontents_len.
    apply N2Nat.inj in Hcontents_len.
    rewrite (Nat.eqb_sym 0 (length contents)).
    subst.

    f_equal.
    f_equal.

    {
      destruct (Nat.eqb_spec (@Datatypes.length (denote_type T) contents) 0)
        as [Hcontents_len_z | Hcontents_len_nz];
        stepsimpl;
        boolsimpl.
        { reflexivity. }
        { try reduce_mod_eqs fifo contents.
          { reflexivity. }
          rewrite Nat2N.id.
          rewrite resize_noop by reflexivity.
          rewrite Hcontents_rev_fifo.
          rewrite rev_length.
          rewrite firstn_length.
          rewrite hd_rev.
          replace (Init.Nat.min (length contents) (length fifo))
            with (length contents) by (rewrite Nat.min_l; lia).
          rewrite <- (firstn_skipn (length contents) fifo) at 1.
          rewrite app_nth1 .
          2:{ cbn.
            rewrite firstn_length.
            replace (Init.Nat.min (length contents) (length fifo))
            with (length contents).
            2:{ rewrite Nat.min_l. {lia. }
              rewrite Nat2N.id in Hcount_bound.
              lia.
            }
            lia.
          }
        rewrite nth_last.
        { reflexivity. }
        rewrite firstn_length.
        replace (Init.Nat.min (length contents) (length fifo))
          with (length contents) by (rewrite Nat.min_l; lia).
        reflexivity.
        }
    }

    destruct (Nat.eqb_spec (@Datatypes.length (denote_type T) contents) 0)
      as [Hcontents_len_z | Hcontents_len_nz];
    destruct input_valid, accepted_output;
      stepsimpl;
      boolsimpl;
      fold denote_type in *;
      try reduce_mod_eqs fifo contents;
      try rewrite app_nil_r;
      try reflexivity;
      try rewrite app_length; cbn.

    all: destr (length contents =? length fifo); try lia; cbn.
    all: repeat match goal with
         | |- context [ ?X ] =>
            lazymatch X with
            | ( N.of_nat ?Y =? N.of_nat ?Z )%N => fail
            | ( N.of_nat ?Y + ?Z =? _ )%N =>
              replace ( N.of_nat Y + Z )%N
              with ( N.of_nat (Y + (N.to_nat Z) ) )%N by now (rewrite Nat2N.inj_add; rewrite N2Nat.id)
            | ( N.of_nat ?Y =? ?Z )%N =>
              replace ( N.of_nat Y =? Z )%N
                with ( N.of_nat Y =? N.of_nat (N.to_nat Z) )%N by now rewrite N2Nat.id
            end
         end.
    all: repeat rewrite eqb_inj.
    all: repeat match goal with
         | |- context [ ?X ] =>
            match X with
            | _ =? _  => destr X; try lia
            end
         end.
    all: try reflexivity.
    all: repeat match goal with
                | H: length (tl ?X) + 1 = _ |- _ =>
                  rewrite tl_length in H; try rewrite nz_s_1_a_1 in H by lia
                | H: length (tl ?X) + 1 <> _ |- _ =>
                  rewrite tl_length in H; try rewrite nz_s_1_a_1 in H by lia
                | H: length (tl ?X) = _ |- _ =>
                  rewrite tl_length in H
                | H: length (tl ?X) <> _ |- _ =>
                  rewrite tl_length in H
                end.
    all: lia.
  Qed.

End FifoSpec.

Section RealignerSpec.
  Local Open Scope N.

  Lemma mask_1000 x:
    x < 2 ^ 32 -> N.land x 0xFF000000 = N.shiftl (N.shiftr x 24) 24.
  Proof.
    clear. intros.
    apply N.bits_inj.
    cbv [N.eqf]; intros.
    rewrite N.land_spec.

    replace n with (N.of_nat (N.to_nat n)) by now rewrite N2Nat.id.
    remember (N.to_nat n) as n'.
    clear Heqn' n.

    destr (n' <? 32)%nat.
    { do 32 (destruct n'; [push_Ntestbit; now boolsimpl| ]); lia. }
    {
      push_Ntestbit; boolsimpl.
      rewrite N.sub_add by lia.
      repeat rewrite (N.testbit_high_lt _ _ _ H) by lia.
      now boolsimpl.
    }
  Qed.

  Lemma mask_1100 x:
    x < 2 ^ 32 -> N.land x 0xFFFF0000 = N.shiftl (N.shiftr x 16) 16.
  Proof.
    clear. intros.
    apply N.bits_inj.
    cbv [N.eqf]; intros.
    rewrite N.land_spec.

    replace n with (N.of_nat (N.to_nat n)) by now rewrite N2Nat.id.
    remember (N.to_nat n) as n'.
    clear Heqn' n.

    destr (n' <? 32)%nat.
    { do 32 (destruct n'; [push_Ntestbit; now boolsimpl| ]); lia. }
    {
      push_Ntestbit; boolsimpl.
      rewrite N.sub_add by lia.
      repeat rewrite (N.testbit_high_lt _ _ _ H) by lia.
      now boolsimpl.
    }
  Qed.

  Lemma mask_1110 x:
    x < 2 ^ 32 -> N.land x 0xFFFFFF00 = N.shiftl (N.shiftr x 8) 8.
  Proof.
    clear. intros.
    apply N.bits_inj.
    cbv [N.eqf]; intros.
    rewrite N.land_spec.

    replace n with (N.of_nat (N.to_nat n)) by now rewrite N2Nat.id.
    remember (N.to_nat n) as n'.
    clear Heqn' n.

    destr (n' <? 32)%nat.
    { do 32 (destruct n'; [push_Ntestbit; now boolsimpl| ]); lia. }
    {
      push_Ntestbit; boolsimpl.
      rewrite N.sub_add by lia.
      repeat rewrite (N.testbit_high_lt _ _ _ H) by lia.
      now boolsimpl.
    }
  Qed.

  Lemma fold_left_4_byte_suffix x xs:
    (length xs = 4)%nat ->
    exists e: {X:N | X < 2 ^ 32},
    (fold_left
       (fun (acc : N) (b3 : Byte.byte) => N.lor (N.shiftl acc 8) (Byte.to_N b3))
       xs x)
    = N.lor (N.shiftl x 32) (proj1_sig e).
  Proof.
    intros.
    destruct xs; [easy|].
    destruct xs; [easy|].
    destruct xs; [easy|].
    destruct xs; [easy|].
    destruct xs; [|easy].
    eexists (x:= exist (fun n => n < 2 ^ 32)
       (N.lor
       (N.lor
          (N.lor (N.shiftl (N.shiftl (N.shiftl (Byte.to_N b) 8) 8) 8)
             (N.shiftl (N.shiftl (Byte.to_N b0) 8) 8))
          (N.shiftl (Byte.to_N b1) 8)) (Byte.to_N b2))
        _
    ).
    cbn.
    intros.
    apply N.bits_inj; cbv [N.eqf]; intros.
    push_Ntestbit.
    destr (n <? 32).
    { rewrite N.shiftl_spec_low with (n:=32) by lia.
      destr (n <? 8).
      { push_Ntestbit. shelve. }
      { push_Ntestbit.
        destr (n <? 16).
        { rewrite N.shiftl_spec_low.
          { shelve. }
          { lia. }
        }
        push_Ntestbit.
        destr (n <? 24).
        { rewrite N.shiftl_spec_low.
          { shelve. }
          { lia. }
        }
        push_Ntestbit.
        repeat rewrite Bool.orb_false_l.
        repeat rewrite <- N.shiftl_spec_high by lia.
        repeat rewrite <- N.lor_spec.
        reflexivity.
      }
    }
    push_Ntestbit.
    repeat rewrite testbit_byte by lia.
    repeat rewrite <- N.sub_add_distr.
    repeat rewrite Bool.orb_false_r.
    cbn.
    reflexivity.

    Unshelve.
    { repeat rewrite N.shiftl_shiftl.
      cbn.
      change 4294967296 with (2^32).

      repeat (
        change (2^32) with (N.max (2^32) (2^32));
        apply N.lor_lt);
        try rewrite N.shiftl_mul_pow2.

        { apply (N.lt_le_trans _ (2 ^ 8 * 2 ^ 24)); try (cbn; lia).
          { apply N.mul_lt_mono_pos_r. { now cbn. }
            cbn.
            pose (Byte.to_N_bounded b).
            lia.
          }
        }
        { apply (N.lt_le_trans _ (2 ^ 8 * 2 ^ 16)); try (cbn; lia).
          { apply N.mul_lt_mono_pos_r. { now cbn. }
            cbn.
            pose (Byte.to_N_bounded b0).
            lia.
          }
        }
        { apply (N.lt_le_trans _ (2 ^ 8 * 2 ^ 8)); try (cbn; lia).
          { apply N.mul_lt_mono_pos_r. { now cbn. }
            cbn.
            pose (Byte.to_N_bounded b1).
            lia.
          }
        }
        pose (Byte.to_N_bounded b2).
        cbn; lia.
    }

    all: push_Ntestbit;
         repeat rewrite Bool.orb_false_l; reflexivity.
  Qed.

  Lemma shiftr_concat_bytes_4 (x: list Byte.byte):
    (length x < 8)%nat ->
    N.shiftr (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 x)) (N.of_nat 32) =
    BigEndianBytes.concat_bytes (List.resize Byte.x00 4 x).
  Proof.
    cbv [BigEndianBytes.concat_bytes].
    intros.
    Ltac t :=
      cbn -[N.shiftr ];
      repeat rewrite N.lor_0_r;
      repeat rewrite N.shiftl_shiftl;
      try rewrite N.shiftr_shiftl_l by lia;
      try rewrite N.shiftl_0_r;
      try now cbn.
    destruct x; [t|
    destruct x; [t|
    destruct x; [t|
    destruct x; [t|]]]].

    repeat rewrite resize_cons.
    cbn [fold_left].
    pose (fold_left_4_byte_suffix
       (N.lor
          (N.shiftl
             (N.lor
                (N.shiftl
                   (N.lor (N.shiftl (N.lor (N.shiftl 0 8) (Byte.to_N b)) 8)
                      (Byte.to_N b0)) 8) (Byte.to_N b1)) 8)
          (Byte.to_N b2))
        (List.resize Byte.x00 4 x)
    ).
    destruct e.
    { apply resize_length. }
    rewrite H0.
    cbn -[N.shiftr].
    rewrite N.shiftr_lor.
    rewrite N.shiftr_shiftl_l by lia.
    assert (N.shiftr (@proj1_sig N (fun X : N => (X < 4294967296)%N) x0) 32 = 0%N).
    { rewrite N.shiftr_eq_0; [reflexivity|].
      destruct x0.
      cbn [proj1_sig].
      destr (x0 =? 0)%N.
      { rewrite E. now cbn. }
      apply N.log2_lt_pow2.
      { lia. }
      apply l.
    }
    rewrite H1.
    rewrite N.lor_0_r.
    rewrite N.shiftl_0_r.
    reflexivity.
  Qed.

  Lemma bytes_to_N_id_4 xs:
    BigEndianBytes.N_to_bytes 4 (BigEndianBytes.concat_bytes (List.resize Byte.x00 4 xs)) = xs.
  Admitted.

  Lemma concat_bytes_4_bound xs: 
    BigEndianBytes.concat_bytes (List.resize Byte.x00 4 xs) < 2 ^ 32.
  Admitted.

  Lemma concat_bytes_8_bound xs: 
    BigEndianBytes.concat_bytes (List.resize Byte.x00 8 xs) < 2 ^ 64.
  Admitted.

  Lemma concat_bytes_skip_4_of_8_spec xs n:
      (length xs < 8)%nat -> 
      n < 32 ->
        N.testbit
          (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 (skipn 4 xs))) n = false.
  Admitted.

  Lemma concat_bytes_lower_8_zero xs n:
      (length xs < 4)%nat -> 
      n < 32 ->
        N.testbit
          (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 xs)) n = false.
  Admitted.

  Lemma concat_bytes_skip_lower_is_upper xs n:
        32 <= n -> n < 64 ->
        N.testbit (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 xs))
          (n - 32) =
        N.testbit
          (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 (skipn 4 xs)))
          n.
  Admitted.

  Lemma concat_bytes_8_is_64bit xs n:
        64 <= n -> 
        N.testbit
          (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 xs))
          n = false.
  Admitted.

  Lemma concat_bytes_truncation x:
    (N.shiftr
      (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 x))
      (N.of_nat 32) mod 2 ^ N.of_nat 32)%N 
      = BigEndianBytes.concat_bytes (List.resize Byte.x00 4 x).
  Admitted.

  Definition realign_inner_spec
    (existing: list Byte.byte) data data_mask := (
      let '(a,b,c,d) :=
        match BigEndianBytes.N_to_bytes 4 data with
        | a::b::c::d::_ => (a,b,c,d)
        | _ => (Byte.x00,Byte.x00,Byte.x00,Byte.x00)
        end in
      existing ++
           if data_mask =? 0x0 then []
      else if data_mask =? 0x1 then [d]
      else if data_mask =? 0x2 then [c]
      else if data_mask =? 0x4 then [b]
      else if data_mask =? 0x8 then [a]
      else if data_mask =? 0x3 then [c;d]
      else if data_mask =? 0x6 then [b;c]
      else if data_mask =? 0xC then [a;b]
      else if data_mask =? 0x9 then [b;c;d]
      else if data_mask =? 0xE then [a;b;c]
      else [a;b;c;d]
      )%N.

  Definition realign_inner_pre
    existing'
    (input : denote_type (input_of (realign_inner (var:=denote_type) )))
    :=
    let '(existing, (existing_len, (data, (data_mask, tt)))) := input in
    existing < 2 ^ 32 /\
    existing_len < 4 /\
    data < 2 ^ 32 /\
    existing' = (firstn (N.to_nat existing_len) (BigEndianBytes.N_to_bytes 4 existing)).

  Lemma step_realign_inner
    existing'
    (input : denote_type (input_of (realign_inner (var:=denote_type) )))
    (state : denote_type (state_of (realign_inner (var:=denote_type) ))):
    realign_inner_pre existing' input ->
    step realign_inner state input =
    let aligned := realign_inner_spec existing' (fst (snd (snd input))) (fst (snd (snd (snd input)))) in
    (tt, (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 aligned), N.of_nat (length aligned))).
  Proof.
    destruct input as (existing, (existing_len, (input, (input_mask, [])))).
    cbn in state.
    cbv [realign_inner realign_inner_pre realign_inner_spec K bvconcat bvslice bvresize] in *;
      stepsimpl.
    repeat (destruct_pair_let; cbn[fst snd]).
    intros Hpre.
    destruct Hpre as [? [? [? ?]]].
    rewrite H2 in *.

    f_equal.

    cbv [BigEndianBytes.N_to_bytes seq List.map].

    cbn [Nat.add].
    repeat rewrite N.lor_0_r.
    repeat rewrite N.land_ones.

    do 4 rewrite mask_1000 by (try apply N.mod_upper_bound; lia).
    do 3 rewrite mask_1100 by (try apply N.mod_upper_bound; lia).
    do 2 rewrite mask_1110 by (try apply N.mod_upper_bound; lia).

    repeat
      match goal with
      | |- context [N.eqb existing_len ?X] =>
        let H := fresh in destruct (N.eqb_spec existing_len X) as [H|H]; try rewrite H
      | |- context [N.eqb input_mask ?X] =>
        let H := fresh in destruct (N.eqb_spec input_mask X) as [H|H]; try rewrite H
      end;
      try match goal with
      | _: ?X <> 0
      , _: ?X <> 1
      , _: ?X <> 2
      , _: ?X < 4
      |- _ =>
        let H := fresh in
        assert (X = 3) by lia; rewrite H
      end.

    all:
      f_equal;
      try rewrite app_nil_r;
      try rewrite length_app;
      try rewrite firstn_length;
      cbv [firstn N.to_nat Pos.to_nat Pos.iter_op Nat.add];
      cbv [BigEndianBytes.concat_bytes repeat List.resize fold_left List.app fst snd length Nat.sub Init.Nat.min N.of_nat firstn];
      repeat rewrite N2Byte.id;
      cbv [Byte.to_N];
      repeat rewrite N.lor_0_r;
      repeat rewrite N.shiftl_shiftl;
      repeat rewrite N.div2_spec;
      repeat rewrite N.shiftr_shiftr;
      cbn [fst snd Nat.add Nat.sub N.add Pos.add Pos.succ Pos.of_succ_nat].

    Ltac brute :=
      repeat (first
        [
          rewrite Bool.orb_false_l
        | rewrite Bool.orb_false_r
        | rewrite N.shiftl_spec_low by lia
        | rewrite N.mod_pow2_bits_low by lia
        | rewrite N.shiftl_spec_high by lia
        | rewrite N.mod_pow2_bits_high by lia
        | rewrite N.shiftr_spec by lia
        | rewrite N.shiftl_0_l by lia
        | rewrite N.shiftl_0_r by lia
        | rewrite N.lor_0_l by lia
        | rewrite N.lor_0_r by lia
        | rewrite N.shiftr_0_l by lia
        | rewrite N.shiftr_0_r by lia
        | rewrite N.lor_spec by lia
        ]);
        try reflexivity;
        try match goal with
            | |- N.testbit ?i ?X = N.testbit ?i ?Y => f_equal; lia
            end;
        try lia.

    all:
      apply N.bits_inj; cbv [N.eqf]; intros;

      change (0*8) with 0;
      change (256) with (2^8);

      destr (n <? 64); brute;
      destr (n <? 32); brute;
      destr (n <? 24); brute;
      destr (n <? 56); brute;
      destr (n <? 48); brute;
      destr (n <? 16); brute;
      destr (n <? 40); brute;
      destr (n <? 8); brute.

    all:
      rewrite N.testbit_high_lt with (x:=input) (n:=32) by lia;
      rewrite Bool.orb_false_r;
      match goal with
      | |- N.testbit ?i ?X = N.testbit ?i ?Y => f_equal; lia
      end.
  Qed.

  Definition realign_spec
    latched_valid
    latched_bytes
    state_data
    (input : denote_type (input_of (var:=denote_type) realign)) := (
    let '(_, (_, (_, (flush, (consumer_ready, tt))))) := input in

    if negb consumer_ready then
      (latched_valid, (BigEndianBytes.concat_bytes (List.resize Byte.x00 4 latched_bytes), N.of_nat (length latched_bytes)))
    else
      let out := firstn 4 state_data in
      let valid := 4 <=? length state_data in

      let valid_or_flushing := valid || (flush && (1 <=? length state_data)) in

      (valid_or_flushing, (BigEndianBytes.concat_bytes (List.resize Byte.x00 4 out), N.of_nat (length out))))%nat.

  Definition realign_update_state
    state_data
    (input : denote_type (input_of (var:=denote_type) realign)) := (
    let '(data_valid, (data, (data_mask, (flush, (consumer_ready, tt))))) := input in
    if negb consumer_ready then
      state_data
    else
      let state' :=
        if (4 <=? length state_data) || flush then
          skipn 4 state_data
        else state_data in

      if data_valid && negb flush then realign_inner_spec state' data data_mask else state')%nat.

  Definition realign_update_latched_bytes
    (latched_bytes: list Byte.byte)
    state_data
    (input : denote_type (input_of (var:=denote_type) realign))
    :=
    let '(data_valid, (data, (data_mask, (flush, (consumer_ready, tt))))) := input in
    if negb consumer_ready then
      latched_bytes
    else
      firstn 4 state_data.

  Definition realign_update_latched_valid
    (latched_valid: bool)
    (state_data: list Byte.byte)
    (input : denote_type (input_of (var:=denote_type) realign)) := (
    let '(data_valid, (data, (data_mask, (flush, (consumer_ready, tt))))) := input in
    if negb consumer_ready then
      latched_valid
    else
      (4 <=? length state_data) || flush && (1 <=? length state_data))%nat.

  Definition realign_pre
    (input : denote_type (input_of (var:=denote_type) realign))
    (state: denote_type (state_of (var:=denote_type) realign))
    :=
    let '(data_valid, (data, (data_mask, (flush, (consumer_ready, tt))))) := input in

    (data < 2 ^ 32)%N
    .

  Definition realign_invariant
    latched_valid latched_bytes
    (ghost_state: list Byte.byte)
    (state: denote_type (state_of (var:=denote_type) realign))
    :=
    let '(out_valid, (out_data, (out_len, (buff, buff_len)))) := state in

    buff_len = N.of_nat (length ghost_state)
    (* buff_len = N.of_nat (length (firstn 4 ghost_state)) *)
    /\ out_valid = latched_valid
    /\ out_data = BigEndianBytes.concat_bytes (List.resize Byte.x00 4 latched_bytes)
    /\ N.to_nat out_len = length latched_bytes
    (* /\ True *)
    /\ buff = BigEndianBytes.concat_bytes (List.resize Byte.x00 8 ghost_state)
    (* /\ N.shiftr buff (N.of_nat 32) = BigEndianBytes.concat_bytes (firstn 4 ghost_state) *)
    /\ (buff < 2 ^ 64)%N
    /\ (buff_len < 8)%N
    .


  Lemma step_realign_invariant
    latched_valid latched_bytes state_data
    next_latched_valid next_latched_bytes next_state_data
      (input : denote_type (input_of (realign (var:=denote_type) )))
      (state : denote_type (state_of (realign (var:=denote_type) ))) :
    next_state_data = realign_update_state state_data input ->
    next_latched_bytes = realign_update_latched_bytes latched_bytes state_data input ->
    next_latched_valid = realign_update_latched_valid latched_valid state_data input ->
    realign_pre input state ->
    realign_invariant latched_valid latched_bytes state_data state ->
    realign_invariant next_latched_valid next_latched_bytes next_state_data (fst (step realign state input)).
  Proof.
    destruct input as (input_valid, (input_data, (input_mask, (flush, (consumer_ready, []))))).
    destruct state as (out_valid, (out_data, (out_length, (q, q_len)))).
    intros Hst Hlatch Hlatchvalid Hpre Hinv.
    destruct Hinv as [Hbuff_len [Hlatch_valid [Hlatch_bytes [Hlatch_bytes_len [Hfirst_bytes [Hbuf_bound Hbuf_len_bound]]]]]].
(* bvresize bvconcat bvmin bvslice *)
    cbv [realign realign_spec realign_pre realign_invariant realign_update_state realign_update_latched_bytes realign_update_latched_valid K] in *;
    stepsimpl.

    repeat (destruct_pair_let; cbn[fst snd]);
    autorewrite with tuple_if.
    erewrite step_realign_inner.

    2: {
      cbv [realign_inner_pre].
      split.
      { cbv [bvslice bvresize]; stepsimpl; cbn [fst snd].
        destruct ( (4 <=? q_len) || flush)%N;
        rewrite N.land_ones; replace (N.of_nat 32) with 32%N by lia;
        apply N.mod_lt; try lia.
      }
      split.
      { cbn [fst snd].
        destruct ( (4 <=? q_len) )%N eqn:?; boolsimpl.
        {
          replace (2^N.of_nat 4)%N with 16%N by now cbn.
          rewrite N.add_sub_swap by now apply N.leb_le.
          rewrite N.add_mod by lia.
          rewrite N.mod_same by lia.
          rewrite N.add_0_r.
          rewrite N.mod_mod by lia.

          rewrite N.mod_small.
          { apply (N.lt_le_trans _ (8 - 4)%N); lia. }
          lia.
        }
        Search (_ <=? _ = false)%N.
        apply N.leb_gt in Heqb.
        destruct flush; try lia.
      }
      split; [lia|]. reflexivity.
    }

    autorewrite with tuple_if.
    destr consumer_ready; cbn [negb fst snd] in *.
    2: {
      subst.
      rewrite Hlatch_bytes_len.
      tauto.
    }


    assert
      ((N.of_nat (Init.Nat.min
                  (N.to_nat
                     (if (4 <=? N.of_nat (length state_data)) || flush
                      then
                       if 4 <=? N.of_nat (length state_data)
                       then
                        (N.of_nat (length state_data) + 2 ^ N.of_nat 4 - 4)
                        mod 2 ^ N.of_nat 4
                       else 0
                      else N.of_nat (length state_data))) 4))%N
        =
            ((if (4 <=? length state_data)%nat || flush
              then N.of_nat (length state_data - 4)
              else N.of_nat (length state_data)) )%N)
              as Heq1.
    {  destr ((4 <=? N.of_nat (length state_data)));
       destr ((4 <=? length state_data))%nat;
       destruct flush; boolsimpl; try lia; rewrite Nat.min_l;
           rewrite N.add_sub_swap by apply E;
           rewrite N.add_mod by (now cbn);
           rewrite N.mod_same by (now cbn);
           rewrite N.add_0_r;
           rewrite N.mod_mod by (now cbn);
           rewrite N.mod_small; cbn; lia.
    }

    assert ((
            if (4 <=? N.of_nat (length state_data))%N || flush
            then
             if (4 <=? N.of_nat (length state_data))%N
             then
              ((N.of_nat (length state_data) + 2 ^ N.of_nat 4 - 4) mod 2 ^ N.of_nat 4)%N
             else 0%N
             else N.of_nat (length state_data)) =
            (
            if (4 <=? length state_data) || flush
            then N.of_nat (length state_data - 4)
            else N.of_nat (length state_data)))%nat as Heq2.
    {  destr ((4 <=? N.of_nat (length state_data)));
       destr ((4 <=? length state_data))%nat;
       destruct flush; boolsimpl; try lia;
           rewrite N.add_sub_swap by apply E;
           rewrite N.add_mod by (now cbn);
           rewrite N.mod_same by (now cbn);
           rewrite N.add_0_r;
           rewrite N.mod_mod by (now cbn);
           rewrite N.mod_small; cbn; lia.
    }

    ssplit.
    {
      subst; cbn [negb fst snd].
      autorewrite with tuple_if.
      cbv [realign_inner_spec].
      repeat rewrite unfold_N_to_bytes_4.
      push_length.
      repeat rewrite Nat2N.of_nat_if.
      repeat rewrite Nat2N.inj_add.
      repeat rewrite Nat2N.of_nat_if.
      rewrite Heq1.
      rewrite Heq2.

      reflexivity.
    }
    {
      subst;
      destr (1 <=? length state_data)%nat;
      destr (1 <=? N.of_nat (length state_data))%N;
      destr (4 <=? length state_data)%nat;
      destr (4 <=? N.of_nat (length state_data))%N;
      try lia; now boolsimpl.
    }
    { subst; cbv [bvslice bvresize]; stepsimpl; cbn [fst snd].
      rewrite N.land_ones_low.
      { rewrite resize_firstn by lia.
        now rewrite shiftr_concat_bytes_4 by lia.
      }

      apply (N.lt_le_trans _ (N.log2 (N.shiftr (2 ^ 64) (N.of_nat 32)))).
      { compute_expr (N.log2 (N.shiftr (2 ^ 64) (N.of_nat 32)))%N.
        destr (N.shiftr
          (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 state_data))
          (N.of_nat 32)).
        { cbn; lia. }
        apply N.log2_lt_pow2.
        { lia. }
        rewrite <- E.
        change (N.of_nat 32) with 32%N.
        replace (N.shiftr (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 state_data)) 32)
          with ((BigEndianBytes.concat_bytes (List.resize Byte.x00 8 state_data)) / 2 ^ 32)%N
          by now rewrite N.shiftr_div_pow2.
        { apply N.div_lt_upper_bound.
          { lia. }
          { now change (2 ^ 32 * 2 ^ 32)%N with (2^64)%N. }
        }
      }
      now cbn.
    }
    { subst; cbv [bvmin bvslice bvresize]; stepsimpl; cbn [fst snd].
      rewrite apply_if_ext_1.
      repeat rewrite N.land_ones_low.
      {
        rewrite firstn_length.
        destr (N.of_nat (length state_data) <=? 4)%N;
        destr (length state_data <=? 4)%nat; try lia.
      }
      { now cbn. }
      { change 8%N with (2^3)%N in Hbuf_len_bound.
        apply (N.lt_trans _ 3).
        { destr ((0 =? N.of_nat (length state_data))%N).
          { now rewrite <- E. }
          { apply N.log2_lt_pow2;lia. }
        }
        lia.
      }
    }
    { cbv [bvslice bvresize]; stepsimpl; cbn [fst snd].
      subst.
      rewrite Heq2.
      autorewrite with tuple_if.
      cbn [fst snd].
      destruct (input_valid && negb flush).
      { do 3 f_equal.
        destr ( (4 <=? length state_data) )%nat;
        destr ( (4 <=? N.of_nat (length state_data)) )%N;
        try lia; boolsimpl.
        { rewrite N.shiftr_0_r.
          destruct state_data; [cbn in E; contradiction|].
          destruct state_data; [cbn in E; contradiction|].
          destruct state_data; [cbn in E; contradiction|].
          destruct state_data; [cbn in E; contradiction|].
          destruct state_data. { now cbn. }
          destruct state_data.

          Local Ltac bitify :=
            apply Byte2N.inj; rewrite N2Byte.id; apply N.bits_inj; cbv [N.eqf].

          Local Ltac s1 :=
            rewrite <- N.land_ones with (n:=8);
            replace 4294967295 with (N.ones 32) by now cbn;
            push_Ntestbit.
          Local Ltac s2 :=
              repeat (rewrite <- N.add_sub_assoc by lia; cbn);
              repeat rewrite N.add_0_r;
              repeat match goal with
                     | |- context [ N.testbit (Byte.to_N _ ) (?x + ?y)] =>
                      repeat rewrite testbit_byte with (n:= x + y) by lia; boolsimpl
                     end.
          Local Ltac s3 :=
            try reflexivity;
            try (now apply testbit_byte);
            try (symmetry; now apply testbit_byte).

          { cbn -[N.shiftr].
            replace (Pos.to_nat 1) with 1%nat by now cbn.
            rewrite firstn_cons.
            rewrite firstn_O.
            f_equal.
            bitify; intros; s1.
            destr (n <? 8);
              push_Ntestbit;
              boolsimpl; s2; s3.
          }

          destruct state_data.
          { cbn -[N.shiftr].
            replace (Pos.to_nat 2) with 2%nat by now cbn.
            repeat rewrite firstn_cons.
            rewrite firstn_O.
            f_equal; [|f_equal];
              bitify; intros; s1;
              destr (n <? 8);
                push_Ntestbit;
                boolsimpl; s2; s3.
          }
          destruct state_data.
          { cbn -[N.shiftr].
            replace (Pos.to_nat 3) with 3%nat by now cbn.
            repeat rewrite firstn_cons.
            rewrite firstn_O.
            f_equal; [|f_equal;[|f_equal]];
              bitify; intros; s1;
              destr (n <? 8);
                push_Ntestbit;
                boolsimpl; s2; s3.
          }
          cbn in Hbuf_len_bound.
          lia.
        }
        rewrite skipn_all2 by lia.
        destruct flush.
        { rewrite Nat2N.id.
          replace (length state_data - 4)%nat with 0%nat by lia.
          now rewrite firstn_O.
        }
        rewrite shiftr_concat_bytes_4 by lia.
        rewrite N.land_ones_low by (
            destr (BigEndianBytes.concat_bytes (List.resize Byte.x00 4 state_data) =? 0);
            try (rewrite E1; cbn; lia);
            rewrite <- N.log2_lt_pow2 by lia;
            now apply concat_bytes_4_bound).
        rewrite bytes_to_N_id_4.
        rewrite Nat2N.id.
        now rewrite firstn_all.
      }


      destr ( (4 <=? length state_data) )%nat;
      destr ( (4 <=? N.of_nat (length state_data)) )%N;
      try lia; boolsimpl;
      apply N.bits_inj; cbv [N.eqf]; intros; push_Ntestbit; boolsimpl.
      {
        destr (n <? 32); push_Ntestbit; boolsimpl.
        { now rewrite concat_bytes_skip_4_of_8_spec by lia. }
        destr (n <? 64); push_Ntestbit; boolsimpl.
        {
          replace (n - N.of_nat 32 + N.of_nat 0) with (n - 32) by lia.
          now rewrite concat_bytes_skip_lower_is_upper by lia.
        }
        now rewrite concat_bytes_8_is_64bit by lia.
      }
      {
        destr (n <? 32); push_Ntestbit; boolsimpl.
        {
          destruct flush.
          { now rewrite concat_bytes_skip_4_of_8_spec by lia. }
          { now rewrite concat_bytes_lower_8_zero by lia. }
        }
        destruct flush;
        destr (n <? 64); push_Ntestbit; boolsimpl;
        replace (n - N.of_nat 32 + N.of_nat 0) with (n - 32) by lia.
        { now rewrite concat_bytes_skip_lower_is_upper by lia. }
        { now rewrite concat_bytes_8_is_64bit. }
        { now replace (n - N.of_nat 32 + N.of_nat 32) with n by lia. }
        now rewrite concat_bytes_8_is_64bit.
      }
    }
    { cbv [bvslice bvresize]; subst; stepsimpl;
      rewrite Heq2;
      autorewrite with tuple_if;
      cbn [fst snd].
      destruct (input_valid && negb flush).
      { apply concat_bytes_8_bound. }
      rewrite N.land_0_l.
      rewrite N.shiftr_0_r.
      apply (N.lt_le_trans _ (N.max (2^64) (2^64))).
      2:{ lia. }
      apply N.lor_lt with (xs:=64) (ys:=64).
      2:{ lia. }
      rewrite N.shiftl_mul_pow2.
      apply (N.lt_le_trans _ (2^32 * 2^32)).
      2:{ cbn; lia. }
      apply N.mul_lt_mono_pos_r.
      { lia. }
      Search (N.land).
      rewrite N.land_ones.
      apply N.mod_upper_bound.
      lia.
    }

    {
      rewrite Hbuff_len.
      autorewrite with tuple_if;
      cbn [fst snd negb].
      destr (input_valid);
      destr (flush);
      destr (4 <=? length state_data)%nat;
      destr (4 <=? N.of_nat (length state_data))%N;
      boolsimpl; try lia.

      { rewrite N.add_sub_swap by lia.
        cbn [N.of_nat].
        replace (2 ^ 4)%N with (1 * 2 ^ 4)%N at 1 by lia.
        rewrite N.mod_add by now cbn.
        rewrite N.mod_small; cbn; lia.
      }
      { rewrite N.add_sub_swap by lia.
        replace (2 ^ 4)%N with (1 * 2 ^ 4)%N at 1 by lia.
        rewrite N.mod_add by now cbn.
        rewrite N.mod_small by ( cbn; subst; lia ).
        rewrite N.shiftr_0_r.
        cbv [realign_inner_spec ]; subst; stepsimpl;
        autorewrite with tuple_if;
        cbn [fst snd]; rewrite unfold_N_to_bytes_4.
        push_length.
        replace input_mask with (N.of_nat (N.to_nat input_mask)) by apply N2Nat.id.
        remember (N.to_nat input_mask) as x.
        do 14 (destruct x; [cbn; lia|]).
        repeat match goal with
        | |- context [?X =? ?Y] => destr (X =? Y); try lia
        end.
      }
      {
        cbv [realign_inner_spec ]; subst; stepsimpl;
        autorewrite with tuple_if;
        cbn [fst snd]; rewrite unfold_N_to_bytes_4.
        push_length.
        replace input_mask with (N.of_nat (N.to_nat input_mask)) by apply N2Nat.id.
        remember (N.to_nat input_mask) as x.
        do 14 (destruct x; [cbn; lia|]).
        repeat match goal with
        | |- context [?X =? ?Y] => destr (X =? Y); try lia
        end.
      }
      { rewrite N.add_sub_swap by lia.
        replace (2 ^ 4)%N with (1 * 2 ^ 4)%N at 1 by lia.
        rewrite N.mod_add by now cbn.
        rewrite N.mod_small; cbn; lia.
      }
      { rewrite N.add_sub_swap by lia.
        cbn [N.of_nat].
        replace (2 ^ 4)%N with (1 * 2 ^ 4)%N at 1 by lia.
        rewrite N.mod_add by now cbn.
        rewrite N.mod_small; cbn; lia.
      }
    }
  Qed.

  Lemma step_realign
    latched_valid
    latched_bytes
      state_data
      (input : denote_type (input_of (realign (var:=denote_type) )))
      (state : denote_type (state_of (realign (var:=denote_type) ))) :
    realign_pre input state ->
    realign_invariant latched_valid latched_bytes state_data state ->
    snd (step realign state input) = realign_spec latched_valid latched_bytes state_data input.
  Proof.
    destruct input as (input_valid, (input_data, (input_mask, (flush, (consumer_ready, []))))).
    destruct state as (out_valid, (out_data, (out_length, (q, q_len)))).
    intros Hpre Hinv.

    destruct Hinv as [Hbuff_len [Hlatch_valid [Hlatch_bytes [Hlatch_bytes_len [Hfirst_bytes Hbuf_bound]]]]].
    subst.

    cbv [realign realign_spec realign_pre realign_invariant realign_update_state K] in *.
    stepsimpl.

    repeat (destruct_pair_let; cbn[fst snd]).
    autorewrite with tuple_if.
    erewrite step_realign_inner.
    {
      cbn [fst snd].
      rewrite <- Hlatch_bytes_len.
      rewrite N2Nat.id.
      cbv [bvslice bvresize bvmin].
      stepsimpl.
      rewrite resize_firstn by lia.
      rewrite N.land_ones.
      rewrite N.land_ones.
      rewrite concat_bytes_truncation.

      replace
        ((if N.of_nat (length state_data) <=? 4
          then N.of_nat (length state_data)
          else 4) mod 2 ^ N.of_nat 4)%N with
          (N.of_nat (length (firstn 4 state_data))).
      2:{
        destr (length state_data <=? 4)%nat;
        destr (N.of_nat (length state_data) <=? 4); try lia.
        { rewrite firstn_length.
          rewrite Nat.min_r by lia.
          now rewrite N.mod_small by (cbn;lia).
        }
        { rewrite firstn_length.
          rewrite Nat.min_l by lia.
          now rewrite N.mod_small by (cbn;lia).
        }
      }

      destr (1 <=? length state_data)%nat;
      destr (1 <=? N.of_nat (length state_data));
      destr (4 <=? length state_data)%nat;
      destr (4 <=? N.of_nat (length state_data)); try lia;
      reflexivity.
    }
    cbn [realign_inner_pre].
    ssplit.
    {
      cbv [bvslice bvresize bvmin].
      stepsimpl.
      repeat rewrite N.land_ones.
      destruct ((4 <=? N.of_nat (length state_data)) || flush)%N;
      apply N.mod_upper_bound; lia.
    }
    {
      cbv [bvslice bvresize bvmin].
      stepsimpl.
      destr (4 <=? length state_data)%nat;
      destr (4 <=? N.of_nat (length state_data))%N;
      try lia.
      {
        rewrite N.add_sub_swap by lia.
        replace 16%N with (1*16)%N at 1 by lia. rewrite N.mod_add by now cbn.
        rewrite N.mod_small by (cbn; lia).
        destruct flush; cbn; lia.
      }
      destruct flush; cbn; lia.
    }
    { easy. }
    { reflexivity. }
  Qed.

End RealignerSpec.

