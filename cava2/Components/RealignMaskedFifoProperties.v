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
  Context (Hfifo_nz: 1 < fifo_size).

  Hint Extern 0 (1 < fifo_size) => apply Hfifo_nz : typeclass_instances .
  Existing Instance fifo_specification.
  Existing Instance fifo_correctness.
  Existing Instance realign_specification.
  Existing Instance realign_correctness.

  Global Instance realign_masked_fifo_invariant
  : invariant_for (realign_masked_fifo fifo_size) (list N * list Byte.byte * bool * list Byte.byte) :=
      fun state '(fifo_contents, realign_contents, realign_latch_valid, realign_latch_bytes)  =>
        let '(state, (realign_state, fifo_state)) := state in
        let '(is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))) := state in
        fifo_invariant (BitVec 32) fifo_size fifo_state fifo_contents
        /\ realign_invariant realign_state (realign_latch_valid, realign_latch_bytes, realign_contents)
        /\ (if fifo_full then length fifo_contents = fifo_size else length fifo_contents < fifo_size)
        /\ (if fifo_empty then length fifo_contents = 0 else length fifo_contents <> 0)
        .

  Instance realign_masked_fifo_specification
  : specification_for (realign_masked_fifo fifo_size) (list N * list Byte.byte * bool * list Byte.byte) :=
    {|
      reset_repr := ([], [], false, []);
      update_repr :=
        fun (input: denote_type (input_of (realign_masked_fifo fifo_size)))
           '(fifo_contents, realign_contents, realign_latch_valid, realign_latch_bytes) =>

        let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in
        let fifo_full := length fifo_contents =? fifo_size in
        let fifo_empty := length fifo_contents =? 0 in

        (* When full, data is ignored and the circuit only performs dequeuing from
         * the FIFO *)
        if fifo_full then
          (if consumer_ready then tl fifo_contents else fifo_contents, realign_contents
          , realign_latch_valid
          , realign_latch_bytes
          )
        else
          (* Consume the first 4 bytes as the fifo is ready to accept, or if
           * told to drain and fifo has finished draining *)
          let realign_contents' :=
            if (4 <=? length realign_contents) then skipn 4 realign_contents else
              if drain && fifo_empty && consumer_ready then skipn 4 realign_contents else
              realign_contents
          in
          let realign_contents_cat :=
              if data_valid then
                if drain
                then realign_contents'
                else realign_inner_spec realign_contents' data data_mask
              else realign_contents'
          in

          let fifo_contents_cat := (if consumer_ready then tl fifo_contents else fifo_contents) ++
            (* If we have 4 bytes in the realigner, concat into a new word and push it into the fifo *)
              if 4 <=? length (realign_contents) then
                if drain
                then []
                else [BigEndianBytes.concat_bytes (firstn 4 realign_contents)]
              else []
          in

          ( fifo_contents_cat
          , realign_contents_cat
          , if 4 <=? length realign_contents then true
              else if drain && consumer_ready && fifo_empty then
                1 <=? length realign_contents
              else false
          , firstn 4 realign_contents
          );

       precondition :=
        fun (input: denote_type (input_of (realign_masked_fifo fifo_size)))
          '(fifo_contents, realign_contents, _, _) =>

        let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in
        (data < 2 ^ 32)%N ;

       postcondition :=
        fun input '(fifo_contents, realign_contents, realign_latch_valid, realign_latch_bytes)
          (output: denote_type (output_of (realign_masked_fifo fifo_size))) =>

        let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in
        let fifo_empty := (length fifo_contents =? 0) in
        let out_data' :=
          if drain
          then if fifo_empty
            then Some (BigEndianBytes.concat_bytes (List.resize Byte.x00 4 (firstn 4 realign_contents)))
            else None
          else hd_error fifo_contents
        in

        exists out_valid out_data out_length is_last fifo_full,
        output = (out_valid, (out_data, (out_length, (is_last, fifo_full))))
        /\ (if consumer_ready then
          (out_valid = if drain
            then if fifo_empty
                 then
                  if 4 <=? length realign_contents then true
                  else if consumer_ready then 1 <=? length realign_contents else false
                 else true
            else if fifo_empty then false else true)
          /\ (match out_data' with None => True | Some x => out_data = x end)
          /\ (if out_valid then
              (if fifo_empty
                then out_length = N.of_nat (length (firstn 4 realign_contents))
                else out_length = 4%N)
              /\ (if drain then if fifo_empty then is_last = true else True else True)
              else True
          )
          else True) ;
    |}.

  Lemma realign_masked_fifo_invariant_preserved : invariant_preserved (realign_masked_fifo fifo_size).
  Proof.
    cbv [invariant_preserved].
    cbn [absorb_any] in *.
    destruct input as (data_valid, (data, (data_mask, (drain, (consumer_ready, []))))).
    destruct state as (state, (realign_state, fifo_state)).
    destruct state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).

    intros input state r new_r; subst.
    simplify_invariant (realign_masked_fifo fifo_size);
      logical_simplify; intros.
    destruct input as (((new_fifo_contents, new_realign_contents), new_latched_valid), new_latched_bytes); logical_simplify.

    cbv [realign_masked_fifo]; stepsimpl; logical_simplify; subst.

    cbv [precondition] in H.
    cbv [realign_masked_fifo_specification update_repr] in H.
    cbn [realign_specification update_repr] in H.
    logical_simplify.

    repeat (destruct_pair_let; cbn [fst snd]).

    lazymatch goal with
      | H : fifo_invariant _ _ ?state ?repr
        |- context [step (fifo _) ?state ?input] =>
          assert (precondition (fifo (T:=BitVec 32) fifo_size) input repr)
      end.
    {
      simplify_spec (fifo (T:=BitVec 32) fifo_size); eauto.
      use_correctness' realign.
      cbn [realign_spec]; boolsimpl.
      autorewrite with tuple_if; cbn [fst].
      destruct fifo_full; boolsimpl; [trivial|].
      destruct_one_match; trivial.
    }

    ssplit.
    {
      use_correctness' realign.
      eapply (invariant_preserved_pf (c:=fifo fifo_size)); cycle 1;
      simplify_spec (fifo (T:=BitVec 32) fifo_size); eauto.
      cbn [denote_type absorb_any] in *; f_equal.

      simplify_spec (realign_masked_fifo fifo_size).
      simplify_spec realign.
      simplify_spec (fifo (T:=BitVec 32) fifo_size).
      simplify_invariant realign.

      cbv [realign_update_latched_valid realign_update_latched_bytes realign_spec realign_invariant'] in *.
      destruct realign_state as (?,(?,(?,(?,?)))).
      logical_simplify.

      autorewrite with tuple_if; cbn [fst snd]; destruct fifo_full; subst;
        [rewrite Nat.eqb_refl|]; boolsimpl; listsimpl; [reflexivity|].

      replace ( length new_fifo_contents =? fifo_size ) with false by
        ( apply eq_sym; apply Nat.eqb_neq; lia); boolsimpl.

      f_equal.
      destruct drain;
        boolsimpl; listsimpl; [ now rewrite Tauto.if_same | ].

      destruct_one_match; [rewrite resize_firstn_alt|]; try lia; reflexivity.
    }
    {
      cbn [fst snd].
      eapply (invariant_preserved_pf (c:=realign)); eauto.
      simplify_spec (realign_masked_fifo fifo_size).
      simplify_spec realign.
      simplify_invariant realign.
      cbv [realign_invariant realign_invariant'] in *; logical_simplify.
      cbn [fst snd denote_type] in *.
      cbv [realign_update_latched_valid realign_update_latched_bytes realign_update_state].
      boolsimpl.
      destruct realign_state as (?,(?,(?,(?,?)))); logical_simplify.

      autorewrite with tuple_if; cbn [fst snd];
        destruct fifo_full; try rewrite H2; try rewrite Nat.eqb_refl;
        boolsimpl; try reflexivity.
      rewrite <- tup_if.
      f_equal.
      { destr (length new_fifo_contents =? fifo_size); try lia.
        destr (4 <=? length new_realign_contents); boolsimpl; [reflexivity|].
        destruct fifo_empty; destr ((length new_fifo_contents =? 0)); try lia; boolsimpl;
        reflexivity.
      }

      destruct_one_match; try lia.

      destruct drain;
      destruct data_valid;
        destruct fifo_empty;
        destruct consumer_ready;
        boolsimpl; try reflexivity.
      all: destr (length new_fifo_contents =? 0); boolsimpl; try reflexivity; try lia.
      all: now rewrite Tauto.if_same.
    }

    all:
      use_correctness' (fifo (T:=BitVec 32) fifo_size);
      simplify_spec (fifo (T:=BitVec 32) fifo_size);
      use_correctness' realign;
      simplify_spec realign;
      simplify_invariant realign;
      simplify_invariant (fifo (T:=BitVec 32) fifo_size);
      cbv [realign_spec realign_invariant'] in *;
      simplify_spec (realign_masked_fifo fifo_size).
    all:
      assert ( (length new_fifo_contents =? fifo_size) = fifo_full);
      [ destruct fifo_full; subst;
        [ now rewrite Nat.eqb_refl
        | apply Nat.eqb_neq; lia ]
      |];
      assert ( (length new_fifo_contents =? 0) = fifo_empty);
      [ destruct fifo_empty;
        [ rewrite H3; now rewrite Nat.eqb_refl
        | apply Nat.eqb_neq; lia ]
      |]; subst.
    all: revert H4 H7.
    all: autorewrite with tuple_if.
    all: cbn [fst snd] in *.
    all: boolsimpl.

    all: destruct consumer_ready; boolsimpl.
    all: destr (length new_fifo_contents =? fifo_size); boolsimpl.
    all: destr (length new_fifo_contents =? 0); try lia; boolsimpl.
    all: destr ((4 <=? length new_realign_contents)); destruct drain; boolsimpl; intros.
    all: try (push_length; destruct_one_match; lia).
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
    intros (((fifo_contents, realign_contents), realign_latch_valid), realign_latch_bytes).

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

    use_correctness.
    repeat (destruct_pair_let; cbn [fst snd]).

    cbn [fst realign_spec].
    cbv [realign_update_latched_valid realign_update_latched_bytes realign_update_state] in *.
    autorewrite with tuple_if.
    cbn [fst snd].

    lazymatch goal with
      | H : fifo_invariant _ _ ?state ?repr
        |- context [step (fifo _) ?state ?input] =>
          assert (precondition (fifo (T:=BitVec 32) fifo_size) input repr)
      end.
    { simplify_spec (fifo (T:=BitVec 32) fifo_size); eauto.
      destruct (length fifo_contents =? fifo_size); boolsimpl;
        [reflexivity|].
      destruct_one_match; lia.
    }

    use_correctness' (fifo (T:=BitVec 32) fifo_size).
    logical_simplify.
    autorewrite with tuple_if; cbn [fst snd].
    push_length.
    do 5 eexists.
    ssplit.
    { reflexivity. }
    { destruct consumer_ready; [|trivial].
      destruct drain;
        destr (length fifo_contents =? 0);
        boolsimpl.
      {
        destr (length fifo_contents =? fifo_size); boolsimpl; [lia|].
        destruct (4 <=? length realign_contents);
        destruct (1 <=? length realign_contents); split.
        all: boolsimpl; ssplit; try reflexivity.
      }
      { ssplit; trivial. }
      { ssplit; [reflexivity| |reflexivity].
        apply length_zero_iff_nil in E.
        now rewrite E.
      }
      { cbn [negb] in H7; ssplit; try reflexivity.
        destruct fifo_contents.
        { cbn [length] in E. lia. }
        { now cbn [hd_error hd] in *. }
      }
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
