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
Require Import Cava.Util.Tactics.
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
    (input : denote_type (input_of (fifo (var:=denote_type) (T:=T) fifo_size)))
    (state: denote_type (state_of (fifo (var:=denote_type) (T:=T) fifo_size)))
    :=
    let '(valid, (data, (accepted_output,_))) := input in
    let '(_, (_, (fifo, count))) := state in
    (* if count is fifo_size we are full and we shouldn't be receiving  *)
    (if valid then N.to_nat count < fifo_size else Coq.Init.Logic.True).

  Definition fifo_invariant
    (contents: list (denote_type T))
    (state: denote_type (state_of (fifo (var:=denote_type) (T:=T) fifo_size)))
    :=
    let '(_, (_, (fifo, count))) := state in
    fifo_size = length fifo
    /\ N.to_nat count <= fifo_size
    /\ N.to_nat count = length contents
    /\ contents = rev (firstn (length contents) fifo)
  .

  Definition fifo_contents_update (empty full: bool) contents
      (input : denote_type (input_of (fifo (var:=denote_type) (T:=T) fifo_size)))
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
      (input : denote_type (input_of (fifo (var:=denote_type) (T:=T) fifo_size)))
      (state : denote_type (state_of (fifo (var:=denote_type) (T:=T) fifo_size))) :
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
      (input : denote_type (input_of (fifo (var:=denote_type) (T:=T) fifo_size)))
      (state : denote_type (state_of (fifo (var:=denote_type) (T:=T) fifo_size)))
      : denote_type (Bit ** T ** Bit ** Bit) :=
    (negb (0 =? length contents)
    , (if 0 =? length contents then default else hd default contents
    , (length new_contents =? 0
    , length new_contents =? fifo_size)))%nat.

  Lemma step_fifo
      contents new_contents
      (input : denote_type (input_of (fifo (var:=denote_type) (T:=T) fifo_size)))
      (state : denote_type (state_of (fifo (var:=denote_type) (T:=T) fifo_size))) :
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

