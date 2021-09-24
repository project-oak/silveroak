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
  Set Typeclasses Debug.


  Lemma concat_bytes_resize xs:
    length xs <= 4 -> BigEndianBytes.concat_bytes (List.resize Byte.x00 4 xs)
                 = BigEndianBytes.concat_bytes xs.
  Admitted.

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
      fun input contents (output: denote_type (output_of (realign_masked_fifo fifo_size))) =>
        True;
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
      { destruct (length new_fifo_contents =? fifo_size); boolsimpl; try reflexivity.
        {
          revert H4; rewrite H2.
          destr (fifo_size =? 0); boolsimpl; try lia.
          destruct ((4 <=? length new_realign_ghost) && negb drain).
          { intros. lia. }
          { reflexivity. }
        }
      }
      { destruct (length new_fifo_contents =? fifo_size); boolsimpl; try reflexivity.
        destruct fifo_empty; destruct (length new_fifo_contents =? 0); boolsimpl; try reflexivity;
          destruct drain; boolsimpl; try reflexivity;
          (destr (4 <=? length new_realign_ghost); [|reflexivity]); now rewrite resize_firstn_alt by lia.
      }
    }
    {
      eapply (invariant_preserved_pf (c:=realign)); eauto.
      simplify_spec (realign_masked_fifo fifo_size).
      simplify_spec realign.
      simplify_invariant realign.
      cbn [fst snd].
      cbv [realign_update_latched_valid realign_update_latched_bytes realign_update_state].
      autorewrite with tuple_if; cbn [fst snd];
        destruct fifo_full; try rewrite H2; try rewrite Nat.eqb_refl;
        boolsimpl; try reflexivity.
      destr (length new_fifo_contents =? fifo_size); try lia.
      destruct fifo_empty; try rewrite H3; boolsimpl; try reflexivity.
      destr (length new_fifo_contents =? 0); try lia; boolsimpl.
      reflexivity.
    }
    { admit. }
    {
      simplify_spec (realign_masked_fifo fifo_size).
      simplify_spec realign.
      assert ( (length new_fifo_contents =? fifo_size) = fifo_full).
      { destruct fifo_full; subst.
        { now rewrite Nat.eqb_refl. }
        { apply Nat.eqb_neq. lia. }
      }
      assert ( (length new_fifo_contents =? 0) = fifo_empty).
      { destruct fifo_empty.
        { rewrite H3. now rewrite Nat.eqb_refl. }
        { apply Nat.eqb_neq. lia. }
      }
      rewrite H6, H7 in H4.
      cbn [realign_spec].
      use_correctness' realign.
      rewrite H5.
      boolsimpl.
      destruct fifo_full; destruct fifo_empty.
      try rewrite H2, H3, Nat.eqb_refl in *.
      {
      rewrite H5.
      autorewrite with tuple_if.
      (* autorewrite with tuple_if; cbn [fst snd]; *)
      cbv
      destruct fifo_full; try rewrite H2; try rewrite Nat.eqb_refl;
        boolsimpl; push_length.
      rewrite
      use_correctness' (fifo (T:= BitVec 32) fifo_size).
      cbn [fst snd].

  Admitted.




    logical_simplify.
    stepsimpl.
    repeat (destruct_pair_let ; cbn [fst snd]).
    cbn [denote_type absorb_any] in *.
    ssplit.
    {
      apply step_fifo_invariant with (contents:=fifo_contents).
      { apply Hfifo_nz. }
      { now apply Hnew_fifo_contents. }
      { cbv [fifo_pre].
        destruct fifo_state as (?,(?,(?,count))).
        destruct fifo_full.
        { now boolsimpl. }
        { boolsimpl.
          cbv [fifo_invariant] in H.
          logical_simplify.
          rewrite H4.
          match goal with
          | |- if ?B then _ else _ => destruct B
          end.
          { apply H1. }
          trivial.
          }
      }
      apply H.
    }

      {
        destruct r.
        eapply (invariant_preserved_pf (c:=fifo fifo_size) ).
        2:{
          cbn [denote_type] in *; destruct_products.
          cbn [fst snd].
          apply H0l. }
        2:{
          cbv [precondition fifo_specification].
          (* cbn [absorb_any] in *. *)
          pose tktktk as H.
          (* pose proof (output_correct_pf (c:=realign)). *)
          cbv [output_correct postcondition realign_specification] in H.
          cbn [denote_type absorb_any] in *.
          (* destruct input as (?, (?, (?, (?, (?, ?))))). *)
          destruct input as (data_valid, (data, (data_mask, (drain, (consumer_ready, []))))).
          cbn [fst snd].
          specialize (H
            (data_valid,
            (data,
            (data_mask,
            (drain && fst (snd (snd (snd (snd (fst state))))) && consumer_ready,
            (negb (snd (snd (snd (snd (snd (fst state)))))), tt)))))).
          specialize (H (fst (snd state))).
          destruct H.
          (* assert (bool * list Byte.byte * list Byte.byte) by admit. *)

          (* specialize (H H2). *)
          assert (realign_invariant (fst (snd state)) x) .
          { cbv [realign_invariant]. destruct x as ((?,?),?).
            cbv [realign_invariant'].
            destruct state as (state, (realign_state, fifo_state)).
            destruct realign_state as (out_valid, (out_data, (out_len, (buff, buff_len)))).
            cbn [fst snd].

          specialize (H H3).
          assert (
           precondition realign
  (data_valid,
           (data,
           (data_mask,
           (drain && fst (snd (snd (snd (snd (fst state))))) && consumer_ready,
           (negb (snd (snd (snd (snd (snd (fst state)))))), tt)))))
             H2) by admit.
          specialize (H H4).
          destruct H2 as ((latched_valid, latched_bytes), ghost_state).
          cbn [absorb_any denote_type] in *.
          rewrite H.
          cbv [realign_spec].
          destruct state as (state, (realign_state, fifo_state)).
          destruct state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).
          (* destruct_products. *)
          autorewrite with tuple_if.
          cbn [fst snd negb];
          cbv [fifo_invariant] in H0.
          destruct fifo_state as (?, (?, (fifo, count))).
          logical_simplify.
          destruct fifo_full; boolsimpl.
          { trivial. }
          destruct (
           ((4 <=? length ghost_state)
            || drain && fifo_empty && consumer_ready && (1 <=? length ghost_state)) && negb drain).
          { apply H5. }
          trivial.
        }
        cbv [update_repr realign_masked_fifo_specification fifo_specification].
        destruct input as (data_valid, (data, (data_mask, (drain, (consumer_ready, []))))).
        destruct state as (state, (realign_state, fifo_state)).
        destruct state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).
        cbn [fst snd].




        realign_invariant (fst (snd state)) H2) by admit.


        destruct_products.
        rewrite H2.

        match goal with
        | |- context [step ?c ?s ?i]=>
          (* idtac *)
          (* assert ( realign_invariant d10 p) by admit; *)
          (* assert ( realign_pre (d, (d0, (d1, (d2 && d8 && fst d3, (negb d9, tt))))) ) by admit; *)
          (* pose proof (output_correct_pf (c:=c) i s p (ltac:(eauto)) (ltac:(eauto))) *)
          (* generalize dependent (snd (step c s i)); intros; *)
          (* simplify_spec c; logical_simplify *)
        end.
        destruct p as ((?,?),?).
        destruct p.

        subst.



    rewrite (surjective_pairing (step c s i));
          use_correctness.

        }
        admit. }
      {
        rewrite (surjective_pairing (step c s i));

        use_correctness' realign.

        cbv [ update_repr realign_masked_fifo_specification fifo_specification].

        match goal with
        | |- context [ step realign ?X ?Y ] =>
          remember (step realign X Y);
          pose proof (output_correct_pf (c:=realign) Y X (false, [], l0))
        end.
        destruct p as ((?,?),?).
        intros.
        cbn [absorb_any] in *.
        specialize (H X).

        (* simplify_spec (fifo (T:=BitVec 32) fifo_size). *)
        simplify_spec realign.

        destruct enable; [ | reflexivity ].
        change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
        Zify.zify. Z.to_euclidean_division_equations. lia. }
        repeat (destruct_pair_let; cbn [fst snd]).
        destruct realign_masked_fifo_specification.
        destruct fifo_specification.
        cbv [ update_repr].

      cbv [invariant_preserved]. intros (enable,[]) (data,?) value.
      intros; subst. simplify_invariant double_counter.
      cbv [double_counter]. stepsimpl. logical_simplify; subst.
      repeat use_correctness. stepsimpl.
      simplify_spec double_counter.
      ssplit.
      { eapply (invariant_preserved_pf (c:=counter));
          [ | solve [eauto] .. ].
        simplify_spec counter.
        destruct enable; [ | reflexivity ].
        change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.


      use_correctness' (fifo (T:=BitVec 32) fifo_size). stepsimpl.
      simplify_spec (realign_masked_fifo fifo_size).
      ssplit.

      (* simplify_invariant double_counter. *)
      (* simplify_spec double_counter. *)
      (* intros; logical_simplify; subst. *)
      (* cbv [double_counter]. stepsimpl. *)
      (* repeat use_correctness. stepsimpl. *)
      (* f_equal. *)


    (* cbv [fifo_invariant]. cbn [absorb_any]. *)
    simplify_spec (realign_masked_fifo fifo_size).
    intros.
    destruct r.
    destruct new_r.
    destruct input as (data_valid, (data, (data_mask, (drain, (consumer_ready, []))))).
    destruct state as (state, (realign_state, fifo_state)).
    inversion H; clear H.
    destruct state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).
    destruct fifo_state as (?, (?, (?, ?))).
    subst; intros.
    logical_simplify.
    intros.
    repeat (destruct_pair_let; cbn [fst snd]).
    cbv [realign_masked_fifo]; stepsimpl.
    repeat (destruct_pair_let; cbn [fst snd]).
    (* Check fifo. *)
    eapply (invariant_preserved_pf (c:=fifo fifo_size)).
    {
      cbv [update_repr].
      cbv [fifo_specification].
      cbv [fifo_invariant] in H0.
      (* Set Printing Implicit. *)
      (* match goal with *)
      (* | |- context [?X] => *)
      (*   match X with *)
      (*   | snd (step realign _ _) => remember X as p *)
      (*   end *)
      (* end. *)

      (* revert Heqp. *)
    (* simplify_spec realign. *)

    (* Existing Instance realign_. *)

    lazymatch goal with
    | |- context [snd (step realign ?s ?i)] =>
      find_correctness realign;
      pose proof (output_correct_pf (c:=realign) i s)
    end.

    specialize (H (true, [], l0)).

    use_correctness' realign.
    pose proof (output_correct_pf (c:=realign) _ _ ).
    generalize dependent (snd (step realign realign_state
     (data_valid,
     (data,
     (data_mask,
     (drain && fifo_empty && consumer_ready, (negb fifo_full, tt))))))
    ); intros.
    revert H.
    simplify_invariant realign; intros. specialize (H X).  subst. logical_simplify; subst
    use_correctness' realign.

    stepsimpl.

      cbn [update_repr].
    eappy
    kcbn [fst snd].
    logical_simplify.
    repeat use_correctness. stepsimpl.
    ssplit.



      (* cbv [invariant_preserved]. intros (enable,[]) (data,?) value. *)
      (* intros; subst. simplify_invariant double_counter. *)
      (* cbv [double_counter]. stepsimpl. logical_simplify; subst. *)
      repeat use_correctness. stepsimpl.
      simplify_spec double_counter.
      ssplit.
          [ | solve [eauto] .. ].
        simplify_spec counter.
        destruct enable; [ | reflexivity ].



    cbv [realign_masked_fifo K]. stepsimpl. ; subst; intros.
    cbv [Fifo.fifo K]; stepsimpl; push_length.
    autorewrite with Nnat.
    subst.
    cbv []
    intros; logical_simplify; revert H0; subst; intros.

  (* Specification for the 'realign_masked_fifo' component defined in terms of
   * 'fifo_spec' and 'realign_masked_spec'. *)
  Definition realign_masked_fifo_spec
    fifo_contents
    realign_masked_state
    (input : denote_type (input_of (var:=denote_type) (realign_masked_fifo fifo_size))) :=
    let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in

    let fifo_empty := (length fifo_contents =? 0) in
    let fifo_full := (length fifo_contents =? fifo_size) in

    let realign_masked_input := (data_valid, (data, (data_mask, ((drain && fifo_empty && consumer_ready), (negb fifo_full, tt))))) in

    let '(realign_maskeded_valid, (realign_maskeded_data, realign_maskeded_length)) :=
      realign_spec
        (fst (fst realign_masked_state)) (snd (fst realign_masked_state)) (snd realign_masked_state)
        realign_masked_input
    in

    let fifo_input := ( (realign_maskeded_valid && (negb drain) && (negb fifo_full)), (realign_maskeded_data, (consumer_ready, tt))) in

    let new_contents :=
      fifo_contents_update (BitVec 32) fifo_size
        fifo_empty fifo_full fifo_contents fifo_input
    in

    let '(fifo_valid, (fifo_data, (fifo_empty, fifo_full))) :=
      fifo_spec (BitVec 32) fifo_size
        fifo_contents new_contents fifo_input in

    let valid :=
      if drain then fifo_valid || realign_maskeded_valid else fifo_valid in
    let data :=
      if drain && negb fifo_valid then realign_maskeded_data
      else fifo_data in
    let length :=
      if drain && negb fifo_valid then realign_maskeded_length
      else 4%N in

    (valid, (data, (length, (drain && negb fifo_valid && valid, fifo_full)))).

  (* Invariant for the 'realign_masked_fifo' component. *)
  Definition realign_masked_fifo_invariant
    fifo_contents realign_masked_contents
    (state : denote_type (state_of (var:=denote_type) (realign_masked_fifo fifo_size))) :=

    let '(top_state, (realign_masked_state, fifo_state)) := state in
    let '(is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))) := top_state in

    fifo_invariant (BitVec 32) fifo_size fifo_contents fifo_state
    /\ realign_masked_invariant (fst (fst realign_masked_contents)) (snd (fst realign_masked_contents)) (snd realign_masked_contents) realign_masked_state
    (* the only additional invariant we preserve is that we respect fifo_full &
     * fifo_empty *)
    /\ (if fifo_full then fifo_size = length fifo_contents else length fifo_contents < fifo_size)
    /\ (if fifo_empty then length fifo_contents = 0 else length fifo_contents <> 0).


  (* Precondition for the 'realign_masked_fifo' component. *)
  Definition realign_masked_fifo_pre
    (input : denote_type (input_of (realign_masked_fifo fifo_size)))
    (state: denote_type (state_of (realign_masked_fifo fifo_size)))
    :=
    let '(valid, (data, _)) := input in
    let '(_, (realign_masked_state, fifo_state)) := state in
    let '(_, (_, (_, count))) := fifo_state in
    (if valid then N.to_nat count < fifo_size else True)
    /\ (data < 2 ^ 32)%N.

  (* "fifo" state update, not intended to be readable,
     discovered mechanically during the proof below. *)
  Definition realign_masked_fifo_update_fifo_contents
    fifo_contents
    (input : denote_type (input_of (realign_masked_fifo fifo_size)))
    (state : denote_type (state_of (realign_masked_fifo fifo_size))):=
    fifo_contents_update (BitVec 32) fifo_size (length fifo_contents =? 0)
      (length fifo_contents =? fifo_size) fifo_contents
      (fst
         (snd
            (step realign_masked (fst (snd state))
               (fst input,
               (fst (snd input),
               (fst (snd (snd input)),
               (fst (snd (snd (snd input))) &&
                fst (snd (snd (snd (snd (fst state))))) &&
                fst (snd (snd (snd (snd input)))),
               (negb (snd (snd (snd (snd (snd (fst state)))))), tt))))))) &&
       negb (fst (snd (snd (snd input)))) &&
       negb (snd (snd (snd (snd (snd (fst state)))))),
      (fst
         (snd
            (snd
               (step realign_masked (fst (snd state))
                  (fst input,
                  (fst (snd input),
                  (fst (snd (snd input)),
                  (fst (snd (snd (snd input))) &&
                   fst (snd (snd (snd (snd (fst state))))) &&
                   fst (snd (snd (snd (snd input)))),
                  (negb (snd (snd (snd (snd (snd (fst state)))))), tt)))))))),
      (fst (snd (snd (snd (snd input)))), tt))).

  (* "realign_masked" state update, not intended to be readable,
     discovered mechanically during the proof below. *)
  Definition realign_masked_fifo_update_realign_masked_contents
    realign_masked_contents
    (input : denote_type (input_of (realign_masked_fifo fifo_size)))
    (state : denote_type (state_of (realign_masked_fifo fifo_size))) :=
    let '(top_state, _) := state in
    let '(is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))) := top_state in
    ( (
      realign_masked_update_latched_valid (fst (fst realign_masked_contents)) (snd realign_masked_contents)
        (fst input,
        (fst (snd input),
        (fst (snd (snd input)),
        (fst (snd (snd (snd input))) && fifo_empty &&
         fst (snd (snd (snd (snd input)))), (negb fifo_full, tt))))),
      realign_masked_update_latched_bytes (snd (fst realign_masked_contents)) (snd realign_masked_contents)
        (fst input,
        (fst (snd input),
        (fst (snd (snd input)),
        (fst (snd (snd (snd input))) && fifo_empty &&
         fst (snd (snd (snd (snd input)))), (negb fifo_full, tt)))))
      ),
      realign_masked_update_state (snd realign_masked_contents)
        (fst input,
        (fst (snd input),
        (fst (snd (snd input)),
        (fst (snd (snd (snd input))) && fifo_empty &&
         fst (snd (snd (snd (snd input)))), (negb fifo_full, tt)))))
    ).


  Lemma step_realign_masked_fifo_invariant
      fifo_contents
      realign_masked_contents
      new_fifo_contents
      new_realign_masked_contents
      (input : denote_type (input_of (realign_masked_fifo fifo_size)))
      (state : denote_type (state_of (realign_masked_fifo fifo_size))):

    new_fifo_contents = realign_masked_fifo_update_fifo_contents fifo_contents input state ->
    new_realign_masked_contents = realign_masked_fifo_update_realign_masked_contents realign_masked_contents input state ->

    realign_masked_fifo_pre input state ->
    realign_masked_fifo_invariant fifo_contents realign_masked_contents state ->
    realign_masked_fifo_invariant new_fifo_contents new_realign_masked_contents (fst (step (realign_masked_fifo fifo_size) state input)).
  Proof.
    cbv [realign_masked_fifo_invariant realign_masked_fifo].
    destruct state as (top_state, (realign_masked_state, fifo_state)).
    destruct realign_masked_state as (x0,(x1,(x2,(x3,x4)))).
    destruct top_state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).

    intros Hnew_fifo_contents Hnew_realign_masked_contents Hpre H.
    logical_simplify.
    stepsimpl.
    repeat (destruct_pair_let ; cbn [fst snd]).
    cbn [denote_type absorb_any] in *.
    ssplit.
    {
      apply step_fifo_invariant with (contents:=fifo_contents).
      { apply Hfifo_nz. }
      { now apply Hnew_fifo_contents. }
      { cbv [fifo_pre].
        destruct fifo_state as (?,(?,(?,count))).
        destruct fifo_full.
        { now boolsimpl. }
        { boolsimpl.
          cbv [fifo_invariant] in H.
          logical_simplify.
          rewrite H4.
          match goal with
          | |- if ?B then _ else _ => destruct B
          end.
          { apply H1. }
          trivial.
          }
      }
      apply H.
    }
    { eapply step_realign_masked_invariant.
      { now rewrite Hnew_realign_masked_contents. }
      { now rewrite Hnew_realign_masked_contents. }
      { now rewrite Hnew_realign_masked_contents. }
      { cbv [realign_masked_fifo_pre] in Hpre. cbn in input, fifo_state.
        destruct_products.
        now cbn.
      }
      { apply H0. }
    }
    all:
      cbn [fst snd];
      erewrite (step_fifo (BitVec 32) fifo_size) with (new_contents := new_fifo_contents);
      [ | trivial | now rewrite Hnew_fifo_contents |
        cbn in input; destruct_products; cbn [fifo_pre fst snd];
        destruct fifo_full; boolsimpl; try trivial;
          boolsimpl;
          cbv [fifo_invariant] in H;
          logical_simplify;
          rewrite H4;
          match goal with
          | |- if ?B then _ else _ => destruct B
          end; try trivial
      |  apply H ].
    {
      cbv [fifo_spec]; cbn [fst snd].
      cbn [denote_type absorb_any] in *.
      destr (length new_fifo_contents =? fifo_size).
      { now rewrite E. }
      { eapply step_fifo_invariant with (new_contents:=new_fifo_contents) in H.
        { cbv [fifo_invariant] in H.
          destruct (fst (step (fifo fifo_size) _ _)) as (?, (?, (?, ?))).
          logical_simplify.
          cbn [denote_type absorb_any] in *.
          rewrite <- H4 in E.
          rewrite <- H4.
          lia.
        }
        { lia. }
        { rewrite Hnew_fifo_contents. reflexivity. }
        { cbn [fifo_pre fst snd].
          destruct_products.
          cbn in H.
          destruct fifo_full.
          { now boolsimpl. }
          { boolsimpl.
            cbv [fifo_invariant] in H.
            logical_simplify.
            rewrite H4.
            match goal with
            | |- if ?B then _ else _ => destruct B
            end.
            { apply H1. }
            trivial.
          }
        }
      }
    }
    {
      cbv [fifo_spec]; cbn [fst snd].
      cbn [denote_type absorb_any] in *.
      destr (length new_fifo_contents =? 0).
      { now rewrite E. }
      { eapply step_fifo_invariant with (new_contents:=new_fifo_contents) in H.
        { cbv [fifo_invariant] in H.
          destruct (fst (step (fifo fifo_size) _ _)) as (?, (?, (?, ?))).
          logical_simplify.
          cbn [denote_type absorb_any] in *.
          rewrite <- H4 in E.
          rewrite <- H4.
          lia.
        }
        { lia. }
        { rewrite Hnew_fifo_contents. reflexivity. }
        { cbn [fifo_pre fst snd].
          destruct_products.
          cbn in H.
          destruct fifo_full.
          { now boolsimpl. }
          { boolsimpl.
            cbv [fifo_invariant] in H.
            logical_simplify.
            rewrite H4.
            match goal with
            | |- if ?B then _ else _ => destruct B
            end.
            { apply H1. }
            trivial.
          }
        }
      }
    }
  Qed.

  Lemma step_realign_masked_fifo
      fifo_contents
      realign_masked_contents
      (input : denote_type (input_of (realign_masked_fifo fifo_size)))
      (state : denote_type (state_of (realign_masked_fifo fifo_size))):

    realign_masked_fifo_pre input state ->
    realign_masked_fifo_invariant fifo_contents realign_masked_contents state ->
    snd (step (realign_masked_fifo fifo_size) state input) = realign_masked_fifo_spec fifo_contents realign_masked_contents input.
  Proof.
    intros.
    destruct state as (top_state, (realign_masked_state, fifo_state)) eqn:?.
    (* destruct realign_masked_state as (x0,(x1,(x2,(x3,x4)))). *)
    destruct top_state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).
    cbn in input, state.
    cbv [realign_masked_fifo realign_masked_fifo_pre realign_masked_fifo_invariant K] in *.
    intros. logical_simplify. cbn [fst snd] in *.
    stepsimpl.
    repeat (destruct_pair_let; cbn [fst snd]).

    match goal with
    | |- context [snd (step (fifo (T:=BitVec 32) fifo_size) ?X ?Y) ] =>
      remember (snd (step (fifo (T:=BitVec 32) fifo_size) X Y)) as stepped_fifo
    end.
    match goal with
    | |- context [ snd (step realign_masked ?X ?Y) ] =>
      remember (snd (step realign_masked X Y)) as stepped_realign_maskeder
    end.

    assert (length fifo_contents =? fifo_size = fifo_full).
    { destruct fifo_full.
      { rewrite H2. apply Nat.eqb_refl. }
      { apply Nat.eqb_neq. lia. }
    }
    assert (length fifo_contents =? 0 = fifo_empty).
    { destruct fifo_empty.
      { rewrite H3. apply Nat.eqb_refl. }
      { apply Nat.eqb_neq. lia. }
    }

    cbn [denote_type absorb_any] in *.
    rewrite <- Heqstepped_realign_maskeder in *.
    rewrite <- Heqstepped_fifo.

    rewrite step_fifo with
      (T:=BitVec 32) (fifo_size:=fifo_size)
      (contents:=fifo_contents)
      (new_contents:=realign_masked_fifo_update_fifo_contents fifo_contents input state)
      in Heqstepped_fifo; cycle 1.
    { trivial. }
    { subst; reflexivity. }
    { clear Heqstepped_fifo Heqstepped_realign_maskeder.
      (* clear stepped_fifo stepped_realign_maskeder. *)
      cbv [fifo_pre].
      destruct_products.
      destruct fifo_full; boolsimpl.
      { trivial. }
      {
        match goal with
        | |- if ?B then _ else _ => destruct B
        end; try trivial.
        cbn in H0.
        logical_simplify.
        now rewrite H6.
      }
    }
    { trivial. }
    cbv [realign_masked_fifo_update_fifo_contents] in *.

    rewrite step_realign_masked with
      (latched_valid:=fst (fst realign_masked_contents))
      (latched_bytes:=snd (fst realign_masked_contents))
      (state_data:=snd realign_masked_contents)
      in Heqstepped_realign_maskeder, Heqstepped_fifo; cycle 1.
    { cbn [realign_masked_pre]; destruct_products; cbn; trivial. }
    { subst; cbn [fst snd ]. trivial. }
    { cbn [realign_masked_pre]; destruct_products; cbn; trivial. }
    { subst; cbn [fst snd ]. trivial. }

    cbv [realign_masked_fifo_spec].
    destruct input as (data_valid, (data, (data_mask, (drain, (consumer_ready, u))))).
    repeat (destruct_pair_let; cbn [fst snd]).
    destruct u.
    cbn [denote_type absorb_any] in *.
    cbv [realign_masked_fifo_update_fifo_contents] in *.
    cbn [fst snd] in *.
    rewrite Heqd in Heqstepped_fifo; cbn [fst snd] in Heqstepped_fifo.
    rewrite H4 in *.
    rewrite H5 in *.
    rewrite <- Heqstepped_realign_maskeder in *.
    rewrite <- Heqstepped_fifo.
    clear Heqstepped_realign_maskeder Heqstepped_fifo.
    reflexivity.
  Qed.
End RealignMaskedFifo.
