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

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.List.

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Semantics.

Import ExprNotations.

Notation BitVec n := (Vec Bit n).

Section Var.
  Context {var : tvar}.

  Local Open Scope N.

  Definition False := Constant (false: denote_type Bit).
  Definition _0 {sz} := Constant (0: denote_type (BitVec sz)).
  Definition _1 {sz} := Constant (1: denote_type (BitVec sz)).
  Definition _2 {sz} := Constant (2: denote_type (BitVec sz)).

  Axiom prim_and :
    forall {s1 s2},
    Circuit s1 [] Bit ->
    Circuit s2 [] Bit ->
    Circuit (s1++s2) [] Bit.

  Axiom prim_or :
    forall {s1 s2},
    Circuit s1 [] Bit ->
    Circuit s2 [] Bit ->
    Circuit (s1++s2) [] Bit.

  Axiom prim_gte :
    forall {s1 s2 t},
    Circuit s1 [] t ->
    Circuit s2 [] t ->
    Circuit (s1++s2) [] Bit.


  (* TODO(blaxill): is this useful or should they be defined on concrete BitVec) *)
  Class bitlike x :=
  { eq : var x -> var x -> Circuit [] [] Bit
  ; not : var x -> Circuit [] [] x
  ; xor : var x -> var x -> Circuit [] [] x
  ; and : var x -> var x -> Circuit [] [] x
  ; add : var x -> var x -> Circuit [] [] x
  }.

  Axiom slice :
    forall {t n} (start len: nat), Circuit [] [Vec t n] (Vec t len).
  Axiom index :
    forall {t n i}, Circuit [] [Vec t n; BitVec i] t.
  Axiom replace :
    forall {t n i}, Circuit [] [Vec t n; BitVec i; t] (Vec t n).
  Axiom concat :
    forall {t n s1 s2}, Circuit s1 [] t -> Circuit s2 [] (Vec t n) -> Circuit (s1++s2) [] (Vec t (S n)).
  Axiom empty : forall {t}, Circuit [] [] (Vec t 0).

  Axiom value_hole : forall {t}, t.
  Axiom circuit_hole : forall {t}, Circuit [] [] t.

  Axiom rotate_right :
    forall {s1 t n},
    Circuit s1 [] (Vec t n) ->
    nat ->
    Circuit s1 [] (Vec t n).
  Axiom shift_right :
    forall {s1 t n},
    Circuit s1 [] (Vec t n) ->
    nat ->
    Circuit s1 [] (Vec t n).

  (* drop leftmost element and push one element in right side, e.g. shifting left *)
  Axiom shift_in_right :
    forall {s1 s2 t n},
    Circuit s1 [] (Vec t n) ->
    Circuit s2 [] t ->
    Circuit (s1++s2) [] (Vec t n).

  Fixpoint n_tup n t : type :=
    match n with
    | O => Unit
    | S n =>
      match n with
      | O => t
      | _ => Pair t (n_tup n t)
      end
    end.

  Axiom vec_as_tuple : forall {t n}, Circuit [] [Vec t n] (n_tup n t).
End Var.

Module PrimitiveNotations.
  Notation "x && y" := (prim_and x y) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x || y" := (prim_or x y) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x >= y" := (prim_gte x y) (in custom expr at level 19, no associativity) : expr_scope.

  Notation "! x" := (
    Let x (fun v => not v)
  ) (in custom expr at level 20) : expr_scope.
  Notation "x == y" := (
    Let x (fun v1 => Let y (fun v2 => eq v1 v2))
  ) (in custom expr at level 19, no associativity) : expr_scope.
  Notation "x ^ y" := (
    Let x (fun v1 => Let y (fun v2 => xor v1 v2))
  ) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x & y" := (
    Let x (fun v1 => Let y (fun v2 => and v1 v2))
  ) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x + y" := (
    Let x (fun v1 => Let y (fun v2 => add v1 v2))
  ) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x >>> y" := (rotate_right x y) (in custom expr at level 19, no associativity) : expr_scope.
  Notation "x >> y" := (shift_right x y) (in custom expr at level 19, no associativity) : expr_scope.
  Notation "x <<+ y" := (shift_in_right x y) (in custom expr at level 19, no associativity) : expr_scope.

  Notation "x :> y" := (concat x y) (in custom expr at level 19, right associativity) : expr_scope.
  Notation "[ ]" := (empty) (in custom expr at level 19, right associativity) : expr_scope.
End PrimitiveNotations.

Axiom bit_bitlike : forall {var}, bitlike (var:=var) Bit.
Axiom bitvec_bitlike : forall {var n}, bitlike (var:=var)  (BitVec n).
Existing Instance bit_bitlike.
Existing Instance bitvec_bitlike.
