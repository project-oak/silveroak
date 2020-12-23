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

From Coq Require Import Arith.PeanoNat NArith.NArith Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bvector.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import coqutil.Tactics.Tactics.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.SequentialProperties.
Require Import Cava.Lib.UnsignedAdders.

Require Import Tests.SignallingCounter.SignallingCounter.

Definition bvadd {n} (a b : Signal.combType (Vec Bit n)) : Signal.combType (Vec Bit n) :=
  N2Bv_sized n (Bv2N a + Bv2N b).

Definition bvzero {n} : Signal.combType (Vec Bit n) := N2Bv_sized n 0.

Fixpoint signallingCounterSpec
           (input : nat -> combType (Vec Bit 8) * combType Bit)
           (t : nat) : combType (Vec Bit 8) :=
  let feedback := match t with
                  | 0 => bvzero
                  | S t' => signallingCounterSpec input t'
                  end in
  let (n, valid) := input t in
  if valid
  then bvadd n feedback
  else feedback.

Definition addNSpec {n} (a b : seqType (Vec Bit n)) :=
  map2 bvadd a b.

Lemma addNCorrect n (a b : list (Bvector n)) :
  sequential (addN (a, b)) = addNSpec a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : seqsimpl.

Lemma mux2Correct {A} (sel : seqType Bit) (f t : seqType A) :
  sequential (mux2 sel f t) = map2 (fun (sel : bool) ft => if sel then snd ft else fst ft)
                                   sel (combine f t).
Proof.
  intros; cbv [mux2 sequential]. seqsimpl.
  cbv [pairSel pairSelList pairSelBool SequentialCombSemantics].
  apply map2_ext; intros; reflexivity.
Qed.
Hint Rewrite @mux2Correct using solve [eauto] : seqsimpl.

Lemma signallingCounterCorrect (i : list (Bvector 8 * bool)) :
  sequential (signallingCounter i) =
  map (signallingCounterSpec
         (fun n => nth n i (bvzero, false)))
      (seq 0 (length i)).
Proof.
  intros; cbv [signallingCounter].
  eapply loop_invariant_alt
    with (I:=fun t acc feedback =>
               feedback = [nth (t-1) acc bvzero]
               /\ acc = map (signallingCounterSpec
                              (fun n => nth n i (bvzero, false)))
                              (seq 0 t)).
  { (* postcondition hold for nil input, and invariant holds after first step *)

    destruct i; cbn [map seq nth length]; [ reflexivity | ].
    seqsimpl. cbv [addNSpec signallingCounterSpec].
    cbn [combine map2 fst snd]. autorewrite with natsimpl push_nth.
    seqsimpl. split; reflexivity. }
  { (* invariant holds through loop body *)
    intros *; intros [Hfeedback Hacc]. subst.
    cbv zeta; intros. seqsimpl. cbv [addNSpec].
    autorewrite with push_length natsimpl push_nth.
    cbn [repeat app].
    match goal with
    | |- context [Signal.defaultCombValue ?t] =>
      change (Signal.defaultCombValue t) with (@bvzero 8, false)
    end.
    seqsimpl. cbn [combine map2 fst snd].
    autorewrite with push_nth.
    ssplit; [ reflexivity | ].
    rewrite seq_S, map_app. cbn [map].
    autorewrite with natsimpl push_nth.
    destruct t; [ lia | ].
    autorewrite with natsimpl.
    cbn [signallingCounterSpec].
    seqsimpl. reflexivity. }
  { (* invariant implies postcondition *)
    intros *; intros [Hfeedback Hacc]. subst; reflexivity. }
Qed.
