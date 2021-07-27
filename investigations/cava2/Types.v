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
Require Import Coq.Numbers.DecimalString.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.

Inductive type :=
| Unit : type
| Bit  : type
| Nat  : type
| Vec  : type -> nat -> type
| Pair : type -> type -> type
.

Fixpoint denote_type (t: type) :=
  match t with
  | Unit => unit
  | Bit => bool
  | Nat => nat
  | Vec t n =>
    match t with
    | Bit => nat
    | _ => list (denote_type t)
    end
  | Pair x y => (denote_type x * denote_type y)%type
  end.

Definition absorb_any (x y: type) :=
  match x, y with
  | Unit, x => x
  | x, Unit => x
  | _, _ => Pair x y
  end.

Declare Scope circuit_type_scope.
Delimit Scope circuit_type_scope with circuit_type.
Open Scope circuit_type_scope.
Notation "[ ]" := Unit (format "[ ]") : circuit_type_scope.
Notation "[ x ]" := (Pair x Unit) : circuit_type_scope.
Notation "[ x ; y ; .. ; z ]" := (Pair x (Pair y .. (Pair z Unit) ..)) : circuit_type_scope.
Notation "x ** y" := (Pair x y)(at level 60, right associativity) : circuit_type_scope.
Notation "x ++ y" := (absorb_any x y) (at level 60, right associativity): circuit_type_scope.

