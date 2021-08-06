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

Import ListNotations.

(* Primitives have both semantic and netlist implementations *)
Inductive UnaryPrim : type -> type -> Type :=
| UnVecSlice: forall {t n} (start len: nat), UnaryPrim (Vec t n) (Vec t len)

| UnVecRotateRight: forall {t n}, nat -> UnaryPrim (Vec t n) (Vec t n)
| UnVecShiftRight: forall {t n}, nat -> UnaryPrim (Vec t n) (Vec t n)

| UnVecToTuple: forall {t n}, UnaryPrim (Vec t (S n)) (ntuple t n)

| UnBitVecNot: forall {n}, UnaryPrim (BitVec n) (BitVec n)
| UnNot: UnaryPrim Bit Bit
.

Inductive BinaryPrim : type -> type -> type -> Type :=
| BinBitAnd: BinaryPrim Bit Bit Bit
| BinBitOr: BinaryPrim Bit Bit Bit

| BinBitVecGte: forall {n}, BinaryPrim (BitVec n) (BitVec n) Bit

| BinBitVecXor: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)
| BinBitVecAnd: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)
| BinBitVecAddU: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)

| BinVecIndex: forall {t n i}, BinaryPrim (Vec t n) (BitVec i) t
| BinVecCons: forall {t n}, BinaryPrim t (Vec t n) (Vec t (S n))

(* drop leftmost element and push one element in right side, e.g. shifting left *)
| BinVecShiftInRight: forall {t n}, BinaryPrim (Vec t n) t (Vec t n)

| BinEq: forall {x}, BinaryPrim x x Bit

.

Inductive TernaryPrim : type -> type -> type -> type -> Type :=
| TernVecReplace: forall {t n i}, TernaryPrim (Vec t n) (BitVec i) t (Vec t n)
.

Fixpoint drop {A} n (ls: list A): list A :=
  match n with
  | 0 => ls
  | S n' => drop n' (tl ls)
  end.

Fixpoint take {A} n (ls: list (simple_denote_type A)): list (simple_denote_type A) :=
  match n with
  | 0 => []
  | S n' => hd simple_default ls :: take n' ( ls)
  end.

Fixpoint rotate_left {A} n (ls: list A): list A :=
  match n with
  | 0 => ls
  | S n' =>
    match ls with
    | nil => []
    | x :: xs => rotate_left n' (xs ++ [x])
    end
  end.

Fixpoint rotate_right {A} n (ls: list (simple_denote_type A)): list (simple_denote_type A) :=
  match n with
  | 0 => ls
  | S n' =>
    rotate_right n' (last ls simple_default :: removelast ls)
  end.

Definition unary_semantics {x r} (prim: UnaryPrim x r)
  : denote_type x -> denote_type r :=
  match prim in UnaryPrim x r return denote_type x -> denote_type r with
  | @UnVecSlice t _ start len =>
    via_simple (b:=Vec t len) (a:= Vec t _) (fun x => take len (drop start x))
  | UnVecRotateRight n =>
    via_simple (b:=Vec _ _) (a:= Vec _ _) (fun x => rotate_right n x)
  | UnVecShiftRight n =>
    via_simple (b:=Vec _ _) (a:= Vec _ _) (fun x => rotate_left n x)
  | @UnVecToTuple t n =>
    via_simple (a:= Vec _ _) (fun x => vector_as_tuple n t x)
  | @UnBitVecNot n =>
    via_simple (a:= Vec Bit n) (b:=Vec Bit n) (fun x => map negb x)
  | UnNot => fun x => negb x
  end.

Definition binary_semantics {x y r} (prim: BinaryPrim x y r)
  : denote_type x -> denote_type y -> denote_type r :=
  match prim in BinaryPrim x y r return denote_type x -> denote_type y -> denote_type r with
  | BinBitAnd => andb
  | BinBitOr => orb

  | BinBitVecGte => fun x y => (y <=? x)%N

  | @BinBitVecXor n =>
    via_simple2 (a:= Vec Bit n) (b:= Vec Bit n) (c:=Vec Bit n)
    (fun x y => map (fun '(x,y) => xorb x y) (combine x y))
  | @BinBitVecAnd n =>
    via_simple2 (a:= Vec Bit n) (b:= Vec Bit n) (c:=Vec Bit n)
    (fun x y => map (fun '(x,y) => andb x y) (combine x y))
  | @BinBitVecAddU n => fun x y => ((x + y) mod (2 ^ (N.of_nat n)))%N

  | @BinVecIndex t n i =>
    fun x n => simple_denote_to_denote (nth (N.to_nat n) (denote_to_simple_denote x) simple_default)
  | BinVecCons =>
    via_simple2 (b:=Vec _ _) (c:=Vec _ _) (fun x xs => x :: xs)
  | @BinVecShiftInRight t n =>
    via_simple2 (a:= Vec t n) (b:=t) (c:=Vec t _)
    (fun xs x => removelast xs ++ [x])
  | BinEq => eqb
  end%list.

Fixpoint replace {A} n a (ls: list A): list A :=
  match ls with
  | [] => []
  | x :: xs =>
    match n with
    | 0 => a :: xs
    | S n' => x :: replace n' a xs
    end
  end%list.

Definition ternary_semantics {x y z r} (prim: TernaryPrim x y z r)
  : denote_type x -> denote_type y -> denote_type z -> denote_type r :=
  match prim in TernaryPrim x y z r return denote_type x -> denote_type y -> denote_type z -> denote_type r with
  | TernVecReplace => fun ls i x => simple_denote_to_denote (t:=Vec _ _ )
      (replace (N.to_nat i) (denote_to_simple_denote x) (denote_to_simple_denote ls))
  end.

