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
Require Import Cava.Tactics.
Require Import Cava.Monad.CavaMonad.
Require Import Cava.Lib.UnsignedAdders.

Require Import Tests.CountBy.CountBy.

Fixpoint countBySpec' (state: Bvector 8) (i : list (Bvector 8))
                      : list (Bvector 8) :=
  match i with
  | [] => []
  | x::xs =>
    let newState := N2Bv_sized 8 (Bv2N x + Bv2N state) in
    newState :: countBySpec' newState xs
  end.

Definition countBySpec := countBySpec' (N2Bv_sized 8 0).

(* TODO: addN sequential seems to only return one result; shouldn't it be a map2? *)
Definition addNSpec {n} (a b : list (Bvector n)) : list (Bvector n) :=
  match a,b with
  | a :: _, b :: _ => [N2Bv_sized n ((Bv2N a + Bv2N b))]
  | _,_ => []
  end.

Local Ltac seqsimpl_step :=
  first [ progress cbn beta iota delta
                   [fst snd hd sequential loopSeq' loop SequentialSemantics]
        | progress cbv beta iota delta [loopSeq]; seqsimpl_step
        | progress autorewrite with seqsimpl
        | progress destruct_pair_let
        | progress simpl_ident ].
Local Ltac seqsimpl := repeat seqsimpl_step.

(* TODO: rename typeclass arguments *)
Lemma addNCorrect n (a b : list (Bvector n)) :
  sequential (addN (H:=SequentialCombSemantics) a b) = addNSpec a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : seqsimpl.

Lemma countForkStep:
  forall (i : Bvector 8) (s : Bvector 8),
    sequential (countFork ([i], [s]))
    = (countBySpec' s [i], countBySpec' s [i]).
Proof.
  intros; cbv [countFork countBySpec'].
  seqsimpl; reflexivity.
Qed.
Hint Rewrite countForkStep using solve [eauto] : seqsimpl.

(* TODO: this should live in a more general location *)
Lemma overlap_nil {A} (x : seqType A) : overlap 0 [] x = x.
Proof. reflexivity. Qed.
Hint Rewrite @overlap_nil using solve [eauto] : seqsimpl.

Lemma countForkCorrect:
  forall (i : list (Bvector 8)) (s : Bvector 8),
    sequential (loopSeq' (countFork (combsemantics:=SequentialCombSemantics)) i [s])
    = (countBySpec' s i, countBySpec' s i).
Proof.
  cbv [sequential]; induction i; intros; [ reflexivity | ].
  seqsimpl. cbn [countBySpec']; rewrite IHi; reflexivity.
Qed.
Hint Rewrite countForkCorrect using solve [eauto] : seqsimpl.

Lemma countByCorrect: forall (i : list (Bvector 8)),
                      sequential (countBy i) = countBySpec i.
Proof.
  intros; cbv [countBy countBySpec].
  seqsimpl. reflexivity.
Qed.
