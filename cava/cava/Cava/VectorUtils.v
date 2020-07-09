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

From Coq Require Import Lists.List.
Import ListNotations.

From Coq Require Import Vector.
Import VectorNotations.

From Coq Require Import ZArith.
Require Import Nat Arith Lia.

From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Traversable.
Require Export ExtLib.Data.Monads.IdentityMonad.

Section traversable.
  Universe u v vF.
  Context {F : Type@{v} -> Type@{vF}}.
  Context {Applicative_F : Applicative F}.
  Context {A : Type@{u}} {B : Type@{v}}.
  Variable f : A -> F B.

  Fixpoint mapT_vector@{} {n} (v : Vector.t A n ) : F (Vector.t B n).
  Proof.
    inversion v.
    exact (@pure F _ _ []%vector).
    refine (
        let _1 := fun y ys => @Vector.cons B y _ ys in
        let _2 := @pure F _ _ _1 in
        let _3 := @ap F _ _ _ _2 (f h) in
        let xs' := mapT_vector _ X in
        let _4 := @ap F _ _ _  _3 in
        _
    ).
    apply _4 in xs' .
    exact xs'.
  Defined.
End traversable.

Definition fixup n (F : Type -> Type) (Ap: Applicative F) (A B : Type) (m: A -> F B) := @mapT_vector F Ap A B m n.

Global Instance Traversable_vector@{} {n} : Traversable (fun t => Vector.t t n) :=
{ mapT := fixup n }.

(******************************************************************************)
(* Vector version of combine                                                  *)
(******************************************************************************)

Local Open Scope vector_scope.

Fixpoint vcombine {A B: Type} {s: nat} (a: Vector.t A s) 
                                       (b: Vector.t B s) :
                                       Vector.t (A * B) s :=

  match s, a, b with
  | O, _, _ => []
  | S n, a, b => let (x, xs) := Vector.uncons a in
                 let (y, ys) := Vector.uncons b in
                 (x, y) :: vcombine xs ys
  end.

Local Close Scope vector_scope.

(* Vector version of seq *)

Program Definition vseq (start len: nat) : Vector.t nat len :=
  Vector.of_list (List.seq start len).
Next Obligation.
  rewrite List.seq_length. reflexivity.
Defined.

(******************************************************************************)
(* Slicing a Vector.t                                                         *)
(******************************************************************************)

Import EqNotations.

Fixpoint sliceVector {T: Type} {s: nat} (v: Vector.t T s) (startAt len : nat)
                     (H: startAt + len <= s) : Vector.t T len :=
  match Nat.eq_dec s (startAt + (s - startAt)) with 
    | left Heq =>
      let '(_, v) := Vector.splitat startAt (rew [fun x => Vector.t T x] Heq in v)
      in
        match Nat.eq_dec (s-startAt) (len + ((s-startAt) - len)) with 
        | left Heq => fst (Vector.splitat len (rew [fun x => Vector.t T x] Heq in v))
        | right Hneq => (ltac:(abstract lia))
        end
    | right Hneq => (ltac:(abstract lia))
    end.

(* An experimental alternative vector representation *)

Fixpoint AltVector (A: Type) (n: nat) : Type :=
  match n with
  | 0 => unit
  | S m => (A * AltVector A m)%type
  end.

Definition v1 : AltVector nat 3 := (1, (2, (3, tt))).

Fixpoint altVectorToList {A: Type} {n: nat} (v: AltVector A n) : list A :=
  match n, v with
  | 0, _ => []%list
  | _, (x, v) => x :: altVectorToList v
  end.

Lemma vecConsFactL: forall (A: Type) (n: nat),
      (A * AltVector A n)%type = AltVector A (n+1).
Proof.
  induction n.
  - auto.
  - simpl. rewrite IHn. reflexivity.
Qed.

Definition vecConsFact {A: Type} {n: nat} (v: A * AltVector A n) :
                                              AltVector A (n+1).
Proof.
  induction n.
  - auto.
  - simpl. rewrite Nat.add_1_r. apply v.
Qed.
                                                
Program Definition consAltVector {A: Type} {n: nat} (a: A) (v: AltVector A n) :
                         AltVector A (n+1) :=
   vecConsFact (a, v).

Lemma length_cons: forall A (x:A) (xs: list A), length (x :: xs) = length xs + 1.
Proof.
  induction xs.
  - simpl. reflexivity.
  - simpl. rewrite <- IHxs. simpl. reflexivity.
Qed.  

Definition vec_cons {A} {x: A} {xs: list A} (v: AltVector A (length xs + 1)) :
                    AltVector A (length (x :: xs)).
Proof.
  rewrite length_cons.
  apply v.
Qed.

Fixpoint listToAltVector {A: Type} (l: list A) : AltVector A (length l) :=
  match l return AltVector A (length l)  with
  | [] => tt
  | x::xs => vec_cons (consAltVector x (listToAltVector xs))
  end.