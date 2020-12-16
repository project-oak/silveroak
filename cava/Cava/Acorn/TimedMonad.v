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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monads.
Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

(**** Monad representing an infinite stream of values ****)

Definition timed (A : Type) : Type := nat -> A.

Instance Monad_timed : Monad timed :=
  {| ret := fun _ x t => x;
     bind :=
       fun A B (x : timed A) (f : A -> timed B) t =>
         f (x t) t
  |}.

Definition asList {A} (x : timed A) (n : nat) := List.map x (seq 0 n).

(* Create a timed monad from a start state and step function *)
Definition timedFix {A} (f : A -> A) (x : A) : timed A :=
  fix body (t : nat) :=
    match t with
    | 0 => x
    | S t' => f (body t')
    end.

(* Stateful version of timedFix; given a start state and a timed input, loop a
   function over state and input to produce a timed output. *)
Definition timedFold {A B} (f : A -> B -> A) (x : A) (y : timed B) : timed A :=
  fix body (t : nat) :=
    match t with
    | 0 => x
    | S t' => f (body t') (y t')
    end.

Section Examples.
  (* Simple timed definition that returns the timestep *)
  Let countUp : timed nat := fun t => t.

  (* If we compute the first five results of countUp, we should get 0...4 *)
  Goal (asList countUp 5 = [0;1;2;3;4]).
  Proof. reflexivity. Qed.

  (* Multiplication *)
  Let multiply (x y : nat) : timed nat := ret (x * y).

  (* If we multiply two countUps, we should get a list of squares *)
  Goal (asList (x <- countUp ;;
                y <- countUp ;;
                multiply x y) 5 = [0;1;4;9;16]).
  Proof. vm_compute. reflexivity. Qed.

  (* Delays the input stream one step *)
  Let delayNat (x : timed nat) : timed nat :=
    fun t =>
      match t with
      | 0 => 0
      | S t' => x t'
      end.

  (* If we delay one of the countUps, we should get 0*0, 0*1, 1*2, 2*3, 3*4 *)
  Goal (asList
          (x <- delayNat countUp ;;
           y <- countUp ;;
           multiply x y) 5 = [0;0;2;6;12]).
  Proof. vm_compute. reflexivity. Qed.

  (* If we delay both inputs to multiply, we should get the list of squares but
     delayed one step. *)
  Goal (asList
          (x <- delayNat countUp ;;
           y <- delayNat countUp ;;
           multiply x y) 5 = [0;0;1;4;9]).
  Proof. vm_compute. reflexivity. Qed.

  (* counter that increments state by 1 each timestep *)
  Let counter : timed nat := timedFix (Nat.add 1) 0.

  Goal (asList counter 5 = [0;1;2;3;4]).
  Proof. vm_compute. reflexivity. Qed.

  (* counter that adds the input to the state *)
  Let countBy : timed nat -> timed nat := timedFold Nat.add 0.

  Goal (asList (countBy countUp) 10 = [0;0;1;3;6;10;15;21;28;36]).
  Proof. vm_compute. reflexivity. Qed.

End Examples.

Section Proofs.
  Lemma timedFold_fold_left {A B} (f : A -> B -> A) a bs t :
    (timedFold f a bs) t = fold_left f (asList bs t) a.
  Proof.
    cbv [asList].
    revert t a bs; induction t; [ reflexivity | ].
    intros. cbn [timedFold]. rewrite seq_S.
    rewrite map_app, fold_left_app. cbn [fold_left map].
    rewrite IHt; reflexivity.
  Qed.
End Proofs.
