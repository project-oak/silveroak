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

From Coq Require Import NArith.NArith Vectors.Vector.
Require Import Coq.Bool.Bvector.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Acorn.Identity.
Require Import Cava.Cava.
Require Import Cava.Tactics.
Require Import Cava.Monad.CavaClass.
Require Import Cava.Monad.Combinators.
Require Import Cava.Monad.SequentialV.
Require Import Cava.Lib.UnsignedAdders.

Require Import Tests.CountBy.CountBy.

Local Open Scope vector_scope.

Fixpoint countBySpec' {ticks : nat} (state: Bvector 8)
  : Vector.t (Bvector 8) ticks -> Vector.t (Bvector 8) ticks :=
  match ticks as ticks0 return _ ticks0 -> _ ticks0 with
  | 0 => fun _ => []
  | S ticks' =>
    fun i =>
      let x := Vector.hd i in
      let xs := Vector.tl i in
      let newState := N2Bv_sized 8 (Bv2N x + Bv2N state) in
      (newState :: countBySpec' newState xs)
  end.

Definition countBySpec {ticks} := @countBySpec' ticks (N2Bv_sized 8 0).

Definition addNSpec {ticks : nat} {n} (a b : Vector.t (Bvector n) ticks)
  : Vector.t (Bvector n) ticks :=
  map2 (fun a b => N2Bv_sized n (Bv2N a + Bv2N b)) a b.

Local Ltac seqsimpl_step :=
  first [ progress cbn beta iota delta
                   [fst snd hd loopSeqV' loop SequentialVectorSemantics]
        | progress cbv beta iota delta [loopSeqV]; seqsimpl_step
        | progress autorewrite with seqsimpl
        | lazymatch goal with
          | |- context [(@SequentialVectorCombSemantics ?ticks)] =>
            progress (change ident with (@cava _ (@SequentialVectorCombSemantics ticks));
                      change @unIdent with (@sequentialV ticks));
            seqsimpl_step
          end
        | progress destruct_pair_let
        | progress simpl_ident ].
Local Ltac seqsimpl := repeat seqsimpl_step.

(* TODO: because sequentialV ignores the ticks argument, using sequentialV
   instead of unIdent means autorewrite doesn't work without explicit ticks. *)

(* TODO: rename typeclass arguments *)
Lemma addNCorrect ticks n (a b : Vector.t (Bvector n) ticks) :
  unIdent (addN (H:=SequentialVectorCombSemantics) (a, b)) = addNSpec a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : seqsimpl.

Lemma countForkStepOnce (ticks: nat) (i s : Vector.t (Bvector 8) 1) :
  sequentialV
    (stepOnce
       (ticks:=ticks)
       (addN >=> fork2)
       (i, s))
  = (countBySpec' (Vector.hd s) i, countBySpec' (Vector.hd s) i).
Proof.
  intros. unfold mcompose. cbv [countBySpec' stepOnce].
  seqsimpl. reflexivity.
Qed.
Hint Rewrite countForkStepOnce using solve [eauto] : seqsimpl.

Lemma countForkCorrect ticks :
  forall(i : Vector.t (Bvector 8) ticks) (s : Vector.t (Bvector 8) 1),
    sequentialV
      (loopSeqV' ticks (stepOnce (ticks:=ticks)
                                 (addN >=> fork2))
                 i s)
    = countBySpec' (Vector.hd s) i.
Proof.
  unfold mcompose. 
  cbv [sequentialV];  
  induction ticks; intros; [ reflexivity | ].
  seqsimpl. cbn [countBySpec']. rewrite IHticks. reflexivity.
Qed.
Hint Rewrite countForkCorrect using solve [eauto] : seqsimpl.

Lemma countByCorrect ticks (i : Vector.t (Bvector 8) ticks) :
  sequentialV (countBy i) = countBySpec i.
Proof.
  unfold mcompose.
  intros; cbv [countBy countBySpec].
  destruct ticks; seqsimpl; [ reflexivity | ].
  seqsimpl. reflexivity.
Qed.
