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

Require Import Lia.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import Cava.Util.Vector.

Inductive type :=
| Unit : type
| Bit : type
| BitVec  : nat -> type
| Vec  : type -> nat -> type
| Pair : type -> type -> type
.

Definition eq_dec_type (x y: type): {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition tvar : Type := type -> Type.
Existing Class tvar.

(* simple_denote_type denotes 'BitVec's as N *)
Instance denote_type : tvar :=
  fix denote_type (t: type) :=
    match t with
    | Unit => unit
    | Bit => bool
    | BitVec n => N
    | Vec t n =>list (denote_type t)
    | Pair x y => (denote_type x * denote_type y)%type
    end.

Fixpoint eqb {t}: denote_type t -> denote_type t -> bool :=
  match t return denote_type t -> denote_type t -> bool with
  | Unit => fun _ _ => true
  | Bit => Bool.eqb
  | BitVec n => N.eqb
  | Vec t n =>
    fun x y =>
      fold_right andb true (map (fun '(x,y) => eqb x y) (combine x y))
  | Pair x y => fun '(x1,y1) '(x2,y2) => andb (eqb x1 x2) (eqb y1 y2)
  end.

Definition absorb_any (x y: type) :=
  match x, y with
  | Unit, x => x
  | x, Unit => x
  | _, _ => Pair x y
  end.

Fixpoint ntuple t n : type :=
  match n with
  | O => t
  | S n => Pair t (ntuple t n)
  end.

Fixpoint default {t: type} : denote_type t :=
  match t return denote_type t with
  | Unit => tt
  | Bit => false
  | BitVec n => 0%N
  | Vec t1 n => List.repeat default n
  | Pair x y => (@default x, @default y)
  end.

Fixpoint vector_as_tuple n t {struct n}
  : denote_type (Vec t (S n)) -> denote_type (ntuple t n) :=
  match n with
  | O => fun x => hd default x
  | S n' => fun ls =>
    (hd default ls, vector_as_tuple _ _ (tl ls))
  end.

Declare Scope circuit_type_scope.
Delimit Scope circuit_type_scope with circuit_type.
Bind Scope circuit_type_scope with type.
Notation "[ ]" := Unit (format "[ ]") : circuit_type_scope.
Notation "[ x ]" := (Pair x Unit) : circuit_type_scope.
Notation "[ x ; y ; .. ; z ]" := (Pair x (Pair y .. (Pair z Unit) ..)) : circuit_type_scope.
Notation "x ** y" := (Pair x y)(at level 60, right associativity) : circuit_type_scope.
Notation "x ++ y" := (absorb_any x y) (at level 60, right associativity): circuit_type_scope.
Arguments denote_type _%circuit_type.
