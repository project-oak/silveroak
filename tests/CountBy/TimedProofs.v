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

From Coq Require Import NArith.NArith Lists.List.
Require Import Coq.Bool.Bvector.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Acorn.Identity.
Require Import Cava.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.ListUtils.
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.Monad.CavaClass.
Require Import Cava.Monad.TimedMonad.
Require Import Cava.Monad.SequentialTimed.
Require Import Cava.Lib.UnsignedAdders.

Require Import Tests.CountBy.CountBy.

(* Need to redefine count-by to use the version of sequential semantics that
   assumes the sequential part is in the monad *)
Section WithCava.
  Context `{semantics:CavaSeqMonad} `{Monad cava}.

  Definition countFork (ab: signal (Vec Bit 8) * signal (Vec Bit 8)) :
                       cava (signal (Vec Bit 8) * signal (Vec Bit 8)) :=
    sum <- addN ab;;
    ret (sum, sum).

  Definition countBy : cava (signal (Vec Bit 8)) -> cava (signal (Vec Bit 8))
    := loopDelaym countFork.
End WithCava.

Definition countBySpec (i : list (Bvector 8)) :=
  fold_left (fun a b => N2Bv_sized 8 (Bv2N a + Bv2N b)) i (N2Bv_sized 8 0).

Definition timed_of_list {A} (default : A) (x : list A) : timed A :=
  fun t => nth t x default.

Definition addNSpec {n} (a b : Bvector n) : Bvector n := N2Bv_sized n (Bv2N a + Bv2N b).

Ltac simpl_timed := cbn [fst snd mcompose bind ret Monad_timed].

Local Ltac seqsimpl_step :=
  first [ progress cbn beta iota delta
                   [fst snd hd sequentialF loopDelaym TimedSeqSemantics]
        | progress cbv beta iota delta [loopSeqF loopSeqF']; seqsimpl_step
        | progress autorewrite with seqsimpl
        | progress destruct_pair_let
        | progress simpl_timed ].
Local Ltac seqsimpl := repeat seqsimpl_step.

(* TODO: rename typeclass arguments *)
Lemma addNCorrect n (a b : Bvector n) t :
  addN (H:=TimedCombSemantics) (a, b) t = addNSpec a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : seqsimpl.

Lemma countForkStep:
  forall (i : Bvector 8) (s : Bvector 8) t,
    countFork (i, s) t = (addNSpec i s, addNSpec i s).
Proof.
  intros; cbv [countFork].
  seqsimpl. reflexivity.
Qed.
Hint Rewrite countForkStep using solve [eauto] : seqsimpl.

Lemma countByCorrect (i : timed (Bvector 8)) t :
  countBy i t = countBySpec (asList i t).
Proof.
  intros; cbv [countBy countBySpec].
  seqsimpl.
  rewrite timedFold_fold_left. factor_out_loops.
  eapply fold_left_double_invariant with (I:= fun x y => x = (y,y)).
  { (* invariant holds at start *)
    reflexivity. }
  { (* invariant holds through loop body *)
    intros; subst. seqsimpl.
    rewrite N.add_comm. reflexivity. }
  { (* invariant implies postcondition *)
    intros; subst. reflexivity. }
Qed.
