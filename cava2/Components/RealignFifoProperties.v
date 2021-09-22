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
Require Import Cava.Components.Fifo.
Require Import Cava.Components.Realigner.
Require Import Cava.Components.RealignFifo.
Require Import Cava.Components.FifoProperties.
Require Import Cava.Components.RealignerProperties.

Import ListNotations.

Local Open Scope bool.
Local Open Scope nat.
Local Open Scope list.

Section RealignFifo.
  Context (fifo_size: nat).
  Context (Hfifo_nz: (1 < fifo_size)%nat).

  (* Specification for the 'realign_fifo' component defined in terms of
   * 'fifo_spec' and 'realign_spec'. *)
  Definition realign_fifo_spec
    fifo_contents
    realign_state
    (input : denote_type (input_of (var:=denote_type) (realign_fifo fifo_size))) :=
    let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in

    let fifo_empty := (length fifo_contents =? 0) in
    let fifo_full := (length fifo_contents =? fifo_size) in

    let realign_input := (data_valid, (data, (data_mask, ((drain && fifo_empty && consumer_ready), (negb fifo_full, tt))))) in

    let '(realigned_valid, (realigned_data, realigned_length)) :=
      realign_spec
        (fst (fst realign_state)) (snd (fst realign_state)) (snd realign_state)
        realign_input
    in

    let fifo_input := ( (realigned_valid && (negb drain) && (negb fifo_full)), (realigned_data, (consumer_ready, tt))) in

    let new_contents :=
      fifo_contents_update (BitVec 32) fifo_size
        fifo_empty fifo_full fifo_contents fifo_input
    in

    let '(fifo_valid, (fifo_data, (fifo_empty, fifo_full))) :=
      fifo_spec (BitVec 32) fifo_size
        fifo_contents new_contents fifo_input in

    let valid :=
      if drain then fifo_valid || realigned_valid else fifo_valid in
    let data :=
      if drain && negb fifo_valid then realigned_data
      else fifo_data in
    let length :=
      if drain && negb fifo_valid then realigned_length
      else 4%N in

    (valid, (data, (length, (drain && negb fifo_valid && valid, fifo_full)))).

  (* Invariant for the 'realign_fifo' component. *)
  Definition realign_fifo_invariant
    fifo_contents realign_contents
    (state : denote_type (state_of (var:=denote_type) (realign_fifo fifo_size))) :=

    let '(top_state, (realign_state, fifo_state)) := state in
    let '(is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))) := top_state in

    fifo_invariant (BitVec 32) fifo_size fifo_contents fifo_state
    /\ realign_invariant (fst (fst realign_contents)) (snd (fst realign_contents)) (snd realign_contents) realign_state
    (* the only additional invariant we preserve is that we respect fifo_full &
     * fifo_empty *)
    /\ (if fifo_full then fifo_size = length fifo_contents else length fifo_contents < fifo_size)
    /\ (if fifo_empty then length fifo_contents = 0 else length fifo_contents <> 0).


  (* Precondition for the 'realign_fifo' component. *)
  Definition realign_fifo_pre
    (input : denote_type (input_of (realign_fifo fifo_size)))
    (state: denote_type (state_of (realign_fifo fifo_size)))
    :=
    let '(valid, (data, _)) := input in
    let '(_, (realign_state, fifo_state)) := state in
    let '(_, (_, (_, count))) := fifo_state in
    (if valid then N.to_nat count < fifo_size else True)
    /\ (data < 2 ^ 32)%N.

  (* "fifo" state update, not intended to be readable,
     discovered mechanically during the proof below. *)
  Definition realign_fifo_update_fifo_contents
    fifo_contents
    (input : denote_type (input_of (realign_fifo fifo_size)))
    (state : denote_type (state_of (realign_fifo fifo_size))):=
    fifo_contents_update (BitVec 32) fifo_size (length fifo_contents =? 0)
      (length fifo_contents =? fifo_size) fifo_contents
      (fst
         (snd
            (step realign (fst (snd state))
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
               (step realign (fst (snd state))
                  (fst input,
                  (fst (snd input),
                  (fst (snd (snd input)),
                  (fst (snd (snd (snd input))) &&
                   fst (snd (snd (snd (snd (fst state))))) &&
                   fst (snd (snd (snd (snd input)))),
                  (negb (snd (snd (snd (snd (snd (fst state)))))), tt)))))))),
      (fst (snd (snd (snd (snd input)))), tt))).

  (* "realign" state update, not intended to be readable,
     discovered mechanically during the proof below. *)
  Definition realign_fifo_update_realign_contents
    realign_contents
    (input : denote_type (input_of (realign_fifo fifo_size)))
    (state : denote_type (state_of (realign_fifo fifo_size))) :=
    let '(top_state, _) := state in
    let '(is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))) := top_state in
    ( (
      realign_update_latched_valid (fst (fst realign_contents)) (snd realign_contents)
        (fst input,
        (fst (snd input),
        (fst (snd (snd input)),
        (fst (snd (snd (snd input))) && fifo_empty &&
         fst (snd (snd (snd (snd input)))), (negb fifo_full, tt))))),
      realign_update_latched_bytes (snd (fst realign_contents)) (snd realign_contents)
        (fst input,
        (fst (snd input),
        (fst (snd (snd input)),
        (fst (snd (snd (snd input))) && fifo_empty &&
         fst (snd (snd (snd (snd input)))), (negb fifo_full, tt)))))
      ),
      realign_update_state (snd realign_contents)
        (fst input,
        (fst (snd input),
        (fst (snd (snd input)),
        (fst (snd (snd (snd input))) && fifo_empty &&
         fst (snd (snd (snd (snd input)))), (negb fifo_full, tt)))))
    ).


  Lemma step_realign_fifo_invariant
      fifo_contents
      realign_contents
      new_fifo_contents
      new_realign_contents
      (input : denote_type (input_of (realign_fifo fifo_size)))
      (state : denote_type (state_of (realign_fifo fifo_size))):

    new_fifo_contents = realign_fifo_update_fifo_contents fifo_contents input state ->
    new_realign_contents = realign_fifo_update_realign_contents realign_contents input state ->

    realign_fifo_pre input state ->
    realign_fifo_invariant fifo_contents realign_contents state ->
    realign_fifo_invariant new_fifo_contents new_realign_contents (fst (step (realign_fifo fifo_size) state input)).
  Proof.
    cbv [realign_fifo_invariant realign_fifo].
    destruct state as (top_state, (realign_state, fifo_state)).
    destruct realign_state as (x0,(x1,(x2,(x3,x4)))).
    destruct top_state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).

    intros Hnew_fifo_contents Hnew_realign_contents Hpre H.
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
    { eapply step_realign_invariant.
      { now rewrite Hnew_realign_contents. }
      { now rewrite Hnew_realign_contents. }
      { now rewrite Hnew_realign_contents. }
      { cbv [realign_fifo_pre] in Hpre. cbn in input, fifo_state.
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

  Lemma step_realign_fifo
      fifo_contents
      realign_contents
      (input : denote_type (input_of (realign_fifo fifo_size)))
      (state : denote_type (state_of (realign_fifo fifo_size))):

    realign_fifo_pre input state ->
    realign_fifo_invariant fifo_contents realign_contents state ->
    snd (step (realign_fifo fifo_size) state input) = realign_fifo_spec fifo_contents realign_contents input.
  Proof.
    intros.
    destruct state as (top_state, (realign_state, fifo_state)) eqn:?.
    (* destruct realign_state as (x0,(x1,(x2,(x3,x4)))). *)
    destruct top_state as (is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))).
    cbn in input, state.
    cbv [realign_fifo realign_fifo_pre realign_fifo_invariant K] in *.
    intros. logical_simplify. cbn [fst snd] in *.
    stepsimpl.
    repeat (destruct_pair_let; cbn [fst snd]).

    match goal with
    | |- context [snd (step (fifo (T:=BitVec 32) fifo_size) ?X ?Y) ] =>
      remember (snd (step (fifo (T:=BitVec 32) fifo_size) X Y)) as stepped_fifo
    end.
    match goal with
    | |- context [ snd (step realign ?X ?Y) ] =>
      remember (snd (step realign X Y)) as stepped_realigner
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
    rewrite <- Heqstepped_realigner in *.
    rewrite <- Heqstepped_fifo.

    rewrite step_fifo with
      (T:=BitVec 32) (fifo_size:=fifo_size)
      (contents:=fifo_contents)
      (new_contents:=realign_fifo_update_fifo_contents fifo_contents input state)
      in Heqstepped_fifo; cycle 1.
    { trivial. }
    { subst; reflexivity. }
    { clear Heqstepped_fifo Heqstepped_realigner.
      (* clear stepped_fifo stepped_realigner. *)
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
    cbv [realign_fifo_update_fifo_contents] in *.

    rewrite step_realign with
      (latched_valid:=fst (fst realign_contents))
      (latched_bytes:=snd (fst realign_contents))
      (state_data:=snd realign_contents)
      in Heqstepped_realigner, Heqstepped_fifo; cycle 1.
    { cbn [realign_pre]; destruct_products; cbn; trivial. }
    { subst; cbn [fst snd ]. trivial. }
    { cbn [realign_pre]; destruct_products; cbn; trivial. }
    { subst; cbn [fst snd ]. trivial. }

    cbv [realign_fifo_spec].
    destruct input as (data_valid, (data, (data_mask, (drain, (consumer_ready, u))))).
    repeat (destruct_pair_let; cbn [fst snd]).
    destruct u.
    cbn [denote_type absorb_any] in *.
    cbv [realign_fifo_update_fifo_contents] in *.
    cbn [fst snd] in *.
    rewrite Heqd in Heqstepped_fifo; cbn [fst snd] in Heqstepped_fifo.
    rewrite H4 in *.
    rewrite H5 in *.
    rewrite <- Heqstepped_realigner in *.
    rewrite <- Heqstepped_fifo.
    clear Heqstepped_realigner Heqstepped_fifo.
    reflexivity.
  Qed.
End RealignFifo.
