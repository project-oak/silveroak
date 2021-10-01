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

  Lemma tktk n xs a b:
    n <= length xs ->
    skipn n (realign_inner_spec xs a b) =
    realign_inner_spec (skipn n xs) a b.
  Proof. Admitted.



  Global Instance realign_masked_fifo_invariant
  : invariant_for (realign_masked_fifo fifo_size) (list N * list Byte.byte * bool) :=
      fun state '(fifo_contents, realign_contents, flush)  =>
        let '(state, (realign_state, fifo_state)) := state in
        let '(is_last, (out_valid, (out_data, (out_length, (fifo_empty, fifo_full))))) := state in

        fifo_invariant (BitVec 32) fifo_size fifo_state fifo_contents
        /\ (
        exists a b, realign_invariant realign_state (a, b, realign_contents))
          (* ( *)
          (* if 4 <=? length realign_contents *)
          (* then true *)
          (* else if flush then if (length fifo_contents =? 0) then true else false else false *)
          (* , firstn 4 realign_contents *)
          (* , skipn 4 realign_contents) *)
        /\ (if fifo_full then length fifo_contents = fifo_size else length fifo_contents < fifo_size)
        /\ (if fifo_empty then length fifo_contents = 0 else length fifo_contents <> 0)
        .

  Instance realign_masked_fifo_specification
  : specification_for (realign_masked_fifo fifo_size) (list N * list Byte.byte * bool) :=
    {| reset_repr := ([], [], false);
     update_repr :=
      fun (input: denote_type (input_of (realign_masked_fifo fifo_size))) '(fifo_contents, realign_contents, flush) =>
      let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in

      let fifo_full := length fifo_contents =? fifo_size in
      let fifo_empty := length fifo_contents =? 0 in

      if fifo_full then
        (if consumer_ready then tl fifo_contents else fifo_contents, realign_contents, drain && consumer_ready)
      else
        let realign_contents_cat :=
            (* (if (4 <=? length realign_contents)%nat || drain && fifo_empty && consumer_ready *)
            (* then skipn 4 realign_contents *)
            (* realign_contents *)
            (* ++ *)
            (if data_valid && consumer_ready then
              realign_inner_spec
                (
                if (4 <=? length realign_contents)%nat then skipn 4 realign_contents else
                  if drain && (length fifo_contents =? 0)%nat then skipn 4 realign_contents else
                  realign_contents
                )


              data data_mask
              (* let '(a,b,c,d) := *)
              (*   match BigEndianBytes.N_to_bytes 4 data with *)
              (*   | a::b::c::d::_ => (a,b,c,d) *)
              (*   | _ => (Byte.x00,Byte.x00,Byte.x00,Byte.x00) *)
              (*   end in *)
              (*        if data_mask =? 0x0 then [] *)
              (*   else if data_mask =? 0x1 then [d] *)
              (*   else if data_mask =? 0x2 then [c] *)
              (*   else if data_mask =? 0x4 then [b] *)
              (*   else if data_mask =? 0x8 then [a] *)
              (*   else if data_mask =? 0x3 then [c;d] *)
              (*   else if data_mask =? 0x6 then [b;c] *)
              (*   else if data_mask =? 0xC then [a;b] *)
              (*   else if data_mask =? 0x9 then [b;c;d] *)
              (*   else if data_mask =? 0xE then [a;b;c] *)
              (*   else [a;b;c;d] *)
            else realign_contents)%N
        in

        let fifo_contents_cat := (if consumer_ready then tl fifo_contents else fifo_contents) ++
            if 4 <=? length (skipn 4 realign_contents) then
              if negb drain
              then [BigEndianBytes.concat_bytes (firstn 4 (skipn 4 realign_contents))]
              else []
            else []
        in

        ( fifo_contents_cat
        , realign_contents_cat
        , drain && consumer_ready);

     precondition :=
      fun (input: denote_type (input_of (realign_masked_fifo fifo_size))) '(fifo_contents, realign_contents, flush) =>

      let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in

      (data < 2 ^ 32)%N
      /\ flush = (drain && consumer_ready)
      ;

     postcondition :=
      fun input '(fifo_contents, realign_contents) (output: denote_type (output_of (realign_masked_fifo fifo_size))) =>
      let '(data_valid, (data, (data_mask, (drain, (consumer_ready, tt))))) := input in
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

    destruct input as ((new_fifo_contents, new_realign_contents), flush); logical_simplify.
    (* destruct new_realign_contents as ((new_latched_valid,new_latched_bytes), new_realign_ghost). *)

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

        destruct_one_match; eauto.
      }
      cbn [denote_type absorb_any] in *; f_equal; rewrite H5.

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

      destruct drain; destruct fifo_empty; destruct data_valid; boolsimpl; listsimpl.

      1-4: now rewrite Tauto.if_same.
      1-4: destruct_one_match; [rewrite resize_firstn_alt|]; try lia; reflexivity.
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
      destruct realign_state as (?,(?,(?,(?,?)))); logical_simplify.

      autorewrite with tuple_if; cbn [fst snd];
        destruct fifo_full; try rewrite H2; try rewrite Nat.eqb_refl;
        boolsimpl; try reflexivity.

      { push_length.
        assert ((fifo_size =? 0) = false) as HX.
        { apply Nat.eqb_neq. lia. }
        assert ((fifo_size - 1 =? 0) = false) as HY.
        { apply Nat.eqb_neq. lia. }
        destruct_one_match.
        { reflexivity. }
        subst; destruct consumer_ready; rewrite HX, ? HY; reflexivity.
      }

      assert (length new_fifo_contents =? fifo_size = false) as HX.
      { apply Nat.eqb_neq. lia. }
      rewrite HX. clear HX.

    destruct data_valid;
      destruct consumer_ready;
      destruct drain;
      boolsimpl;
      push_length; push_firstn.
      8:{ destr (4 <=? length new_realign_contents - 4).

      destruct drain; boolsimpl.
      { admit. }
      destr (4 <=? length new_realign_contents).
      { destr (4 <=? length (realign_inner_spec (skipn 4 new_realign_contents) data data_mask)).
        {


            (* match BigEndianBytes.N_to_bytes 4 data with *)
            (* | [] => (Byte.x00, Byte.x00, Byte.x00, Byte.x00) *)
            (* | [a] => (Byte.x00, Byte.x00, Byte.x00, Byte.x00) *)
            (* | [a; b0] => (Byte.x00, Byte.x00, Byte.x00, Byte.x00) *)
            (* | [a; b0; c] => (Byte.x00, Byte.x00, Byte.x00, Byte.x00) *)
            (* | a :: b0 :: c :: d :: _ => (a, b0, c, d) *)
            (* end ) as X. *)
      destruct X as (((?,?),?),?).
      push_length.

      destruct data_valid;
        destruct consumer_ready;
          boolsimpl; try reflexivity;
      destruct data_mask.


      all: push_length.



        2:{
          push_length. natsimpl.
          destruct drain;
          repeat destruct_one_match; listsimpl. reflexivity.



      f_equal.
      {
        f_equal.
        {
      push_length.



      {


      destruct drain; destruct consumer_ready; boolsimpl.
      {
        subst.
      destr (length new_fifo_contents =? fifo_size); try lia.
      destruct data_valid; boolsimpl.
      2:{

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
