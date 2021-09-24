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
Require Import Cava.Invariant.

Require Import Cava.Components.Fifo.

Import ListNotations.

Local Open Scope bool.
Local Open Scope nat.
Local Open Scope list.

Section FifoSpec.
  Context (T: type).
  Context (fifo_size: nat).
  Context (Hfifo_nz: (1 < fifo_size)%nat).

  Lemma rewrite_if_modulo x y z: x < 2 ^ y ->
    (if 1 <=? x then (x + 2 ^ y - 1) mod 2 ^ y else z) = (if 1 <=? x then x - 1 else z).
  Proof.
    intros.
    rewrite (if_true_rew (1 <=? x) z ((x + 2 ^ y - 1) mod 2 ^ y) (x - 1)); [reflexivity|].
    destruct (Nat.leb_spec0 1 x); try congruence; intros [].
    apply Nat.sub_mod_no_underflow; lia.
  Qed.

  Global Instance fifo_invariant
    : invariant_for (fifo fifo_size) (list (denote_type T)) :=
    fun '(_, (_, (fifo, count))) 'contents =>
    length fifo = fifo_size
    /\ N.to_nat count <= fifo_size
    /\ N.to_nat count = length contents
    /\ contents = rev (firstn (length contents) fifo).

  Instance fifo_specification
    : specification_for (fifo fifo_size) (list (denote_type T)) :=
    {| reset_repr := [];
     update_repr :=
      fun (input: denote_type (input_of (fifo fifo_size))) contents =>
      let '(valid, (data, (accepted_output,_))) := input in
      let empty := length contents =? 0 in
      let full := length contents =? fifo_size in
      ( (if accepted_output && negb empty then tl contents else contents)
        ++ if valid && negb full then [data] else []);

     precondition :=
      fun input contents =>
      let '(valid, _) := input in
      (* if count is fifo_size we are full and we shouldn't be receiving  *)
      (if valid then length contents < fifo_size else True);

     postcondition :=
      fun input contents (output: denote_type (output_of (fifo fifo_size))) =>
        let '(valid, (data, (accepted_output,_))) := input in
        let '(out_valid, (out, (empty, full))) := output in

        let pempty := length contents =? 0 in
        let pfull := length contents =? fifo_size in

        let new_contents :=
          (if accepted_output && negb pempty then tl contents else contents)
          ++ if valid && negb pfull then [data] else [] in

        empty = (length new_contents =? 0)
        /\ full = (length new_contents =? fifo_size)
        /\
        match hd_error contents with
        | Some x => out_valid = true /\ out = x
        | None => out_valid = false
        end;
  |}%nat.

  Lemma fifo_invariant_preserved : invariant_preserved (fifo fifo_size).
  Proof.
    simplify_invariant (fifo (T:=T) fifo_size). cbn [absorb_any].
    simplify_spec (fifo (T:=T) fifo_size).
    intros (data_valid, (data, (accepted_output, []))).
    intros (valid, (output, (fifo, count))).
    intros contents.
    intros; logical_simplify; revert H0; subst; intros.

    cbv [Fifo.fifo K]; stepsimpl; push_length.
    autorewrite with Nnat.

    (* Simplify modular arithmetic *)
    repeat rewrite Bool.andb_if; rewrite H3 in *.
    repeat rewrite rewrite_if_modulo by (
      apply (Nat.le_lt_trans _ (length fifo)); [lia|];
        rewrite H0; apply (Nat.lt_le_trans _ (fifo_size + 1));
        [|apply Nat.log2_up_spec]; lia).
    rewrite le_1_is_0.

    (* Simplify modular arithmetic *)
    destruct data_valid; [
      rewrite Nat.mod_small by
        (apply (Nat.lt_le_trans _ (fifo_size + 1));
          [ now apply Nat.add_lt_mono_r| apply Nat.log2_up_spec; lia ])
      |].

    all:
      fold denote_type in *; destruct accepted_output;
      destr (length contents =? 0);
      match goal with
      | |- context [ length _ =? fifo_size ] => destr ( length contents =? fifo_size )
      | |- _ => idtac
      end;
      boolsimpl; natsimpl.

    all: try rewrite E in *; ssplit; try lia; natsimpl.
    all: try rewrite Nat.sub_add by lia; try rewrite H4;
         push_firstn; listsimpl; push_firstn;
         repeat rewrite <- H4;
         try reflexivity.

    (* Solve remaining list based goals *)
    all:
      rewrite H4 at 1; try rewrite tl_rev;
      try change [data] with (rev [data]);
      try rewrite <- rev_app_distr;
      try rewrite removelast_firstn_len;
      try rewrite firstn_firstn;
      try rewrite <- firstn_app_2;
      try rewrite Nat.min_l by (push_length; rewrite Nat.min_l; lia);
      push_length;
      cbn [List.app];
      try rewrite Nat.min_l by lia;
      try replace (1 + Init.Nat.pred (length contents)) with (length contents) by lia;
      try replace (Init.Nat.pred (length contents)) with (length contents - 1) by lia;
      try replace (1 + length contents) with (length contents + 1) by lia;
      reflexivity.
  Qed.

  Lemma fifo_output_correct : output_correct (fifo fifo_size).
  Proof.
    simplify_invariant (fifo (T:=T) fifo_size). cbn [absorb_any].
    simplify_spec (fifo (T:=T) fifo_size).

    intros (data_valid, (data, (accepted_output, []))).
    intros (valid, (output, (fifo, count))).
    intros contents.
    intros; logical_simplify.

    cbv [Fifo.fifo K]; stepsimpl; push_length.
    autorewrite with Nnat.

    (* Simplify modular arithmetic *)
    repeat rewrite Bool.andb_if; rewrite H2 in *.
    rewrite rewrite_if_modulo by (
      apply (Nat.le_lt_trans _ (length fifo)); [lia|];
        rewrite H; apply (Nat.lt_le_trans _ (fifo_size + 1));
        [|apply Nat.log2_up_spec]; lia).
    rewrite le_1_is_0.

    (* Simplify modular arithmetic *)
    match goal with
    | |- context [ if data_valid then ?A else ?B ] =>
      erewrite (if_true_rew data_valid _ A); [|
        intros; rewrite H4 in H0;
        now rewrite Nat.mod_small by
          (apply (Nat.lt_le_trans _ (fifo_size + 1));
            [ now apply Nat.add_lt_mono_r| apply Nat.log2_up_spec; lia ])
      ]
    end.

    rewrite Bool.negb_andb; boolsimpl; ssplit.

    1-2:
      fold denote_type in *;
        destruct data_valid, fifo_size, accepted_output;
          repeat match goal with
          | |- context [?X =? ?Y] => destr (X =? Y); revert E; boolsimpl
          end; try lia.

    destruct contents; cbn [hd_error]; push_length; boolsimpl.
    { rewrite Nat.eqb_refl; now boolsimpl. }

    repeat match goal with
    | |- context [?X =? ?Y] => destr (X =? Y); revert E; boolsimpl
    end; try lia.

    intros; split; [reflexivity|].
    rewrite Nat.add_sub_swap by lia.
    replace (S (length contents) - 1) with (length contents) by lia.
    rewrite Nat.add_mod by (try apply Nat.pow_nonzero; lia).
    rewrite Nat.mod_same by (try apply Nat.pow_nonzero; lia).
    rewrite Nat.add_0_r.
    rewrite Nat.mod_mod by (try apply Nat.pow_nonzero; lia).
    assert (hd default (d:: contents) = hd default (rev (firstn (length (d :: contents)) fifo))) by
      now rewrite H3 at 1.
    cbn [hd] in H4.
    rewrite H4.
    rewrite Nat.mod_small.
    2: {
      apply (Nat.lt_le_trans _ (fifo_size + 1));
        [ | apply Nat.log2_up_spec; lia ].
        cbn in H1.
        lia.
    }

    rewrite hd_rev.
    rewrite <- nth_firstn_inbounds with (n:=length (d::contents)) by (cbn; lia).
    rewrite nth_last.
    2:{ push_length. rewrite Nat.min_l. { cbn; lia. } apply H1. }
    rewrite resize_noop; [reflexivity | now rewrite <- H].
  Qed.

  Lemma fifo_invariant_at_reset : invariant_at_reset (fifo fifo_size).
  Proof.
    simplify_invariant (fifo (T:=T) fifo_size).
    cbv [fifo]. cbn [reset_state]; stepsimpl.
    ssplit; [ cbv [default]; push_length | | | ]; cbn; try reflexivity; lia.
  Qed.

  Existing Instances fifo_invariant_at_reset fifo_invariant_preserved
           fifo_output_correct.

  Global Instance fifo_correctness : correctness_for (fifo fifo_size).
  Proof. constructor; typeclasses eauto. Defined.

End FifoSpec.

