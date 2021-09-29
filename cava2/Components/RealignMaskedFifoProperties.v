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
Require Import Cava.Components.RealignMasked.
Require Import Cava.Components.RealignMaskedFifo.
Require Import Cava.Components.FifoProperties.
Require Import Cava.Components.RealignMaskedProperties.

Import ListNotations.

Local Open Scope bool.
Local Open Scope nat.
Local Open Scope list.

Section RealignMaskedFifo.
  Context (fifo_size: nat).
  Context (Hfifo_nz: (1 < fifo_size)%nat).

  Hint Extern 0 (1 < fifo_size) => apply Hfifo_nz : typeclass_instances .
  Existing Instance fifo_specification.
  Existing Instance fifo_correctness.
  Existing Instance realign_specification.
  Existing Instance realign_correctness.

  Global Instance realign_masked_fifo_invariant
  : invariant_for (realign_masked_fifo fifo_size) (list N * (bool * list Byte.byte * list Byte.byte)) :=
      fun state '(fifo_contents, realign_contents)  =>
        let '(state, (realign_state, fifo_state)) := state in
        let '(is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))) := state in

        fifo_invariant (BitVec 32) fifo_size fifo_state fifo_contents
        /\ realign_invariant realign_state realign_contents
        /\ (if fifo_full then length fifo_contents = fifo_size else length fifo_contents < fifo_size)
        /\ (if fifo_empty then length fifo_contents = 0 else length fifo_contents > 0)
        .

  Instance realign_masked_fifo_specification
  : specification_for (realign_masked_fifo fifo_size) (list N * (bool * list Byte.byte * list Byte.byte)) :=
    {| reset_repr := ([], (false, [], []));
     update_repr :=
      fun (input: denote_type (input_of (realign_masked_fifo fifo_size))) '(fifo_contents, realign_contents) =>
      let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in

      let fifo_empty := length fifo_contents =? 0 in
      let fifo_full := length fifo_contents =? fifo_size in

      let realign_input :=
        (data_valid, (data, (data_mask, (drain && fifo_empty && consumer_ready, (negb fifo_full, tt))))) in
      let '(realign_valid, realign_data, new_realign_contents) :=
        update_repr (c:=realign) realign_input realign_contents in
      let fifo_input :=
        (realign_valid && negb drain && negb fifo_full, (BigEndianBytes.concat_bytes realign_data, (consumer_ready, tt))) in
      let new_fifo_contents :=
        update_repr (c:=fifo (T:=BitVec 32) fifo_size) fifo_input fifo_contents in

      (new_fifo_contents, (realign_valid, realign_data, new_realign_contents));

     precondition :=
      fun (input: denote_type (input_of (realign_masked_fifo fifo_size))) '(fifo_contents, realign_contents) =>

      let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in

      let fifo_empty := length fifo_contents =? 0 in
      let fifo_full := length fifo_contents =? fifo_size in

      let realign_input :=
        (data_valid, (data, (data_mask, (drain && fifo_empty && consumer_ready, (negb fifo_full, tt))))) in
      let '(realign_valid, realign_data, new_realign_contents) :=
        update_repr (c:=realign) realign_input realign_contents in
      let fifo_input :=
        (realign_valid && negb drain && negb fifo_full, (BigEndianBytes.concat_bytes realign_data, (consumer_ready, tt))) in

      precondition realign realign_input realign_contents
      /\ precondition (fifo (T:=BitVec 32) fifo_size) fifo_input fifo_contents
      ;

     postcondition :=
      fun input '(fifo_contents, realign_contents) (output: denote_type (output_of (realign_masked_fifo fifo_size))) =>
      let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in

      let fifo_empty := (length fifo_contents =? 0) in
      let fifo_full := (length fifo_contents =? fifo_size) in

      let realign_input :=
        (data_valid, (data, (data_mask, (drain && fifo_empty && consumer_ready, (negb fifo_full, tt))))) in
      let '(realign_valid, (realign_data, realign_len)) :=
        realign_spec (fst (fst realign_contents)) (snd (fst realign_contents)) (snd realign_contents) realign_input in

      let fifo_input :=
        (realign_valid && negb drain && negb fifo_full, (realign_data, (consumer_ready, tt))) in

      let new_fifo_contents :=
        update_repr (c:=fifo (T:=BitVec 32) fifo_size) fifo_input fifo_contents in

      let fifo_full := (length new_fifo_contents =? fifo_size) in
      let fifo_valid := 1 <=? length fifo_contents in

      let valid :=
        if drain then fifo_valid || realign_valid else fifo_valid in

      let data :=
        if drain && negb fifo_valid then realign_data
        else hd default fifo_contents in
      let length :=
        if drain && negb fifo_valid then realign_len
        else 4%N in

      if valid then
        output = (valid, (data, (length, (drain && negb fifo_valid && valid, fifo_full))))
      else
        exists unknown,
        output = (valid, (unknown, (length, (drain && negb fifo_valid && valid, fifo_full))));
  |}%nat.

  Lemma realign_masked_fifo_invariant_preserved : invariant_preserved (realign_masked_fifo fifo_size).
  Proof.
    cbv [invariant_preserved].
    cbn [absorb_any] in *.
    destruct input as (data_valid, (data, (data_mask, (drain, (consumer_ready, []))))).
    destruct state as (state, (realign_state, fifo_state)).
    destruct state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).
    intros input state r new_r; subst.
    simplify_invariant (realign_masked_fifo fifo_size); logical_simplify; intros.
    cbv [realign_masked_fifo]; stepsimpl; logical_simplify; subst.
    destruct input as (new_fifo_contents, new_realign_contents); logical_simplify.
    destruct new_realign_contents as ((new_latched_valid,new_latched_bytes), new_realign_ghost).
    cbv [precondition] in H.
    cbv [realign_masked_fifo_specification update_repr] in H.
    cbn [realign_specification update_repr] in H.
    logical_simplify.

    repeat (destruct_pair_let; cbn [fst snd]).
    ssplit.
    {
      use_correctness' realign.
      eapply (invariant_preserved_pf (c:=fifo fifo_size)); cycle 1;
      simplify_spec (fifo (T:=BitVec 32) fifo_size); eauto.
      { use_correctness' realign.
        rewrite H5.
        cbv [realign_spec].
        autorewrite with tuple_if; cbn [fst snd]; boolsimpl.
        simplify_invariant realign; cbv [realign_invariant'] in *; logical_simplify.
        destruct fifo_full; boolsimpl; eauto.

        destruct (((4 <=? length new_realign_ghost)
          || drain && fifo_empty && consumer_ready && (1 <=? length new_realign_ghost)) && negb drain);
          eauto.
      }
      cbn [denote_type absorb_any] in *; f_equal; rewrite H5.

      simplify_spec (realign_masked_fifo fifo_size).
      simplify_spec realign.
      simplify_spec (fifo (T:=BitVec 32) fifo_size).
      cbv [realign_update_latched_valid realign_update_latched_bytes realign_spec] in *.
      autorewrite with tuple_if; cbn [fst snd]; destruct fifo_full; boolsimpl.
      { destr (length new_fifo_contents =? fifo_size); boolsimpl; try reflexivity.
        {
          revert H4; rewrite H2.
          destr (fifo_size =? 0); boolsimpl; try lia.
        }
      }
      { cbn [denote_type].
        destr (length new_fifo_contents =? fifo_size); boolsimpl; try reflexivity.
        destr fifo_empty; destr (length new_fifo_contents =? 0); boolsimpl; try reflexivity;
          destruct drain; boolsimpl; try reflexivity; try lia;
          (destr (4 <=? length new_realign_ghost); [|reflexivity]); now rewrite resize_firstn_alt by lia.
      }
    }
    {
      eapply (invariant_preserved_pf (c:=realign)); eauto.
      simplify_spec (realign_masked_fifo fifo_size).
      simplify_spec realign.
      simplify_invariant realign.
      cbn [fst snd denote_type] in *.
      cbv [realign_update_latched_valid realign_update_latched_bytes realign_update_state].
      autorewrite with tuple_if; cbn [fst snd];
        destruct fifo_full; try rewrite H2; try rewrite Nat.eqb_refl;
        boolsimpl; try reflexivity.
      destr (length new_fifo_contents =? fifo_size); try lia.
      destruct fifo_empty; try rewrite H3; boolsimpl; try reflexivity.
      destr (length new_fifo_contents =? 0); try lia; boolsimpl.
      reflexivity.
    }
    all:
      simplify_spec (realign_masked_fifo fifo_size);
      simplify_spec realign;
      assert ( (length new_fifo_contents =? fifo_size) = fifo_full);
      [ destruct fifo_full; subst;
        [ now rewrite Nat.eqb_refl
        | apply Nat.eqb_neq; lia ]
      |];
      assert ( (length new_fifo_contents =? 0) = fifo_empty);
      [ destruct fifo_empty;
        [ rewrite H3; now rewrite Nat.eqb_refl
        | apply Nat.eqb_neq; lia ]
      |]; cbn [denote_type] in *.
    all:
      rewrite H6, H5 in *;
      cbn [realign_spec];
      use_correctness' realign;
      cbn [denote_type] in *;
      rewrite H7;
      cbn [fst realign_spec];
      cbv [realign_update_latched_valid realign_update_latched_bytes realign_update_state] in *;
      autorewrite with tuple_if;
      cbn [fst snd];
      use_correctness' (fifo (T:= BitVec 32) fifo_size);
      destruct (length new_fifo_contents =? 0);[destruct H5|];
        cbn [denote_type absorb_any] in *; rewrite H5; cbn [fst snd].

    all: boolsimpl; push_length.
    all: repeat rewrite Tauto.if_same.
    all: destruct consumer_ready; destruct (length new_fifo_contents =? 0);
        destruct (length new_fifo_contents =? fifo_size); boolsimpl;
        destruct_one_match; try lia.
    all: destruct_one_match; lia.
  Qed.

  Lemma realign_masked_fifo_output_correct : output_correct (realign_masked_fifo fifo_size).
  Proof.
    simplify_invariant (realign_masked_fifo fifo_size).
    simplify_spec (realign_masked_fifo fifo_size).
    cbn [absorb_any].

    intros (data_valid, (data, (data_mask, (drain, (consumer_ready, []))))).
    intros
      ( (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full)))))
      , ( realign_state
        , fifo_state)).
    destruct realign_state as (?,(?,(?,(?,?)))) eqn:?.
    destruct fifo_state as (?,(?,(?,?))) eqn:?.
    intros (fifo_contents, ((realign_valid, realign_data), realign_contents)).

    cbv [realign_masked_fifo K]; stepsimpl; push_length.

    intros; logical_simplify.

    cbv [update_repr realign_specification] in *; logical_simplify.

    assert ( (length fifo_contents =? fifo_size) = fifo_full);
    [ destruct fifo_full; subst;
      [ now rewrite Nat.eqb_refl
      | apply Nat.eqb_neq; lia ]
    |].
    assert ( (length fifo_contents =? 0) = fifo_empty);
    [ destruct fifo_empty;
      [ rewrite H3; now rewrite Nat.eqb_refl
      | apply Nat.eqb_neq; lia ]
    |]; cbn [denote_type] in *.

    rewrite H6, H5 in *.

    (* use_correctness. *)
    match goal with
    | |- context [ ?X ] =>
      match X with
      | match ?Y with pair _ _ => _ end =>
        match Y with
        | step ?c ?s ?i =>
          find_correctness c;
          rewrite (surjective_pairing Y);
          use_correctness' c
        end
      end
    end.
    rewrite H7; clear H7.

    repeat (destruct_pair_let; cbn [fst snd]).

    cbn [fst realign_spec].
    cbv [realign_update_latched_valid realign_update_latched_bytes realign_update_state] in *.
    autorewrite with tuple_if.
    cbn [fst snd].
    use_correctness' (fifo (T:=BitVec 32) fifo_size).
    simplify_invariant realign.
    simplify_invariant (fifo (T:=BitVec 32) fifo_size).
    cbv [realign_pre realign_invariant'] in *.
    logical_simplify.
    destruct (length fifo_contents =? 0);[destruct H5|]; rewrite H5; clear H5; cbn [fst snd].
    1:
      destr (
       if drain
       then
        (1 <=? length fifo_contents)
        || (if negb (negb (length fifo_contents =? fifo_size))
            then realign_valid
            else
             (4 <=? length realign_contents)
             || drain && true && consumer_ready && (1 <=? length realign_contents))
       else 1 <=? length fifo_contents
       ).
    3:
      destr (
       if drain
       then
        (1 <=? length fifo_contents)
        || (if negb (negb (length fifo_contents =? fifo_size))
            then realign_valid
            else
             (4 <=? length realign_contents)
             || drain && false && consumer_ready && (1 <=? length realign_contents))
       else 1 <=? length fifo_contents
       ).

    { revert E; rewrite H3; destruct drain; destruct consumer_ready; boolsimpl;
        destr (0=?fifo_size); try lia;
        destr (1<=?0); try lia.
      all: intro Hx; rewrite Hx; boolsimpl.
      all: reflexivity.
    }
    {
      generalize dependent E.
      rewrite H3; destruct drain; destruct consumer_ready; boolsimpl;
        destr (0=?fifo_size); try lia;
        destr (1<=?0); try lia.
      1-2: intro Hx; eexists; rewrite Hx; reflexivity.
      all: intros _; eexists; reflexivity.
    }
    { revert E; destruct drain; destruct consumer_ready; boolsimpl;
        destr (1 <=? length fifo_contents); try lia.
      all: boolsimpl; reflexivity.
    }
    {
      generalize dependent E.
      destruct drain; destruct consumer_ready; boolsimpl;
        destr (1 <=? length fifo_contents); try lia.
     }
  Qed.

  Lemma realign_masked_fifo_at_reset : invariant_at_reset (realign_masked_fifo fifo_size).
  Proof.
    simplify_invariant (realign_masked_fifo fifo_size).
    simplify_invariant (fifo (T:=BitVec 32) fifo_size).
    simplify_invariant realign.
    repeat destruct_pair_let; cbn [fst snd].
    ssplit; cbn; try reflexivity.
    1: push_length.
    all: cbn; ssplit; lia.
  Qed.

  Existing Instances realign_masked_fifo_at_reset realign_masked_fifo_invariant_preserved
           realign_masked_fifo_output_correct.

  Global Instance realign_masked_fifo_correctness : correctness_for (realign_masked_fifo fifo_size).
  Proof. constructor; typeclasses eauto. Defined.

End RealignMaskedFifo.
