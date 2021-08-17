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
Require Import Cava.Util.List.
Require Import Cava.Types.
Import ListNotations.

(* Primitives have both semantic and netlist implementations *)
Inductive UnaryPrim : type -> type -> Type :=
| UnVecSlice: forall {t n} (start len: nat), UnaryPrim (Vec t n) (Vec t len)
| UnVecResize: forall {t n m}, UnaryPrim (Vec t n) (Vec t m)
| UnVecReverse: forall {t n}, UnaryPrim (Vec t n) (Vec t n)
| UnVecUncons: forall {t n}, UnaryPrim (Vec t (S n)) (t ** Vec t n)

| UnBitVecResize: forall {n m}, UnaryPrim (BitVec n) (BitVec m)
| UnBitVecShiftRight: forall {n}, nat -> UnaryPrim (BitVec n) (BitVec n)
| UnBitVecShiftLeft: forall {n}, nat -> UnaryPrim (BitVec n) (BitVec n)

| UnVecToTuple: forall {t n}, UnaryPrim (Vec t (S n)) (ntuple t n)

| UnBitVecNot: forall {n}, UnaryPrim (BitVec n) (BitVec n)

| UnBitNot: UnaryPrim Bit Bit
.

Inductive BinaryPrim : type -> type -> type -> Type :=
| BinBitOr: BinaryPrim Bit Bit Bit
| BinBitAnd: BinaryPrim Bit Bit Bit

| BinBitVecGte: forall {n}, BinaryPrim (BitVec n) (BitVec n) Bit

| BinBitVecOr: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)
| BinBitVecXor: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)
| BinBitVecAnd: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)
| BinBitVecAddU: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)
| BinBitVecSubU: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)
| BinBitVecMax: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)
| BinBitVecMin: forall {n}, BinaryPrim (BitVec n) (BitVec n) (BitVec n)

| BinVecIndex: forall {t n i}, BinaryPrim (Vec t n) (BitVec i) t
| BinVecCons: forall {t n}, BinaryPrim t (Vec t n) (Vec t (S n))
| BinVecConcat: forall {t n m}, BinaryPrim (Vec t n) (Vec t m) (Vec t (n + m))

(* drop leftmost element and push one element in right side, e.g. shifting left *)
| BinVecShiftInRight: forall {t n}, BinaryPrim (Vec t n) t (Vec t n)
| BinVecShiftInLeft: forall {t n}, BinaryPrim t (Vec t n) (Vec t n)

| BinEq: forall {x}, BinaryPrim x x Bit

.

Inductive TernaryPrim : type -> type -> type -> type -> Type :=
| TernVecReplace: forall {t n i}, TernaryPrim (Vec t n) (BitVec i) t (Vec t n)
.

Definition unary_semantics {x r} (prim: UnaryPrim x r)
  : denote_type x -> denote_type r :=
  match prim in UnaryPrim x r return denote_type x -> denote_type r with
  | @UnVecSlice t n start len =>
    fun x => resize default len (firstn len (skipn start x))
  | @UnVecResize t n m => fun x => resize default m x
  | @UnVecReverse t n => fun x => rev x

  | @UnVecUncons t n => fun x => (hd default x, tl x)

  | @UnBitVecResize n m => fun x => N.land x (N.ones (N.of_nat m))
  | UnBitVecShiftRight n => fun x => N.shiftr x (N.of_nat n)
  | @UnBitVecShiftLeft sz n => fun x => ((N.shiftl x (N.of_nat n)) mod (2 ^ (N.of_nat sz)))%N

  | @UnVecToTuple t n => vector_as_tuple n t
  | @UnBitVecNot n => fun x => N.lnot x (N.of_nat n)

  | UnBitNot => negb
  end.

Definition binary_semantics {x y r} (prim: BinaryPrim x y r)
  : denote_type x -> denote_type y -> denote_type r :=
  match prim in BinaryPrim x y r return denote_type x -> denote_type y -> denote_type r with
  | BinBitOr => orb
  | BinBitAnd => andb

  | BinBitVecGte => fun x y => (y <=? x)%N

  | @BinBitVecOr n => N.lor
  | @BinBitVecXor n => N.lxor
  | @BinBitVecAnd n => N.land
  | @BinBitVecAddU n => fun x y => ((x + y) mod (2 ^ (N.of_nat n)))%N
  | @BinBitVecSubU n => fun x y => ((x + 2 ^ N.of_nat n - y) mod (2 ^ (N.of_nat n)))%N
  | @BinVecIndex t len i => fun x n => nth (N.to_nat n) (resize default len x) default
  | @BinBitVecMax n => fun x y => (if x <=? y then y else x)%N
  | @BinBitVecMin n => fun x y => (if x <=? y then x else y)%N
  | BinVecCons => fun x y => x :: y
  | BinVecConcat => fun x y => x ++ y
  | @BinVecShiftInRight t n => (fun xs x => tl (xs ++ [x]))
  | @BinVecShiftInLeft t n => (fun x xs => removelast (x :: xs))
  | BinEq => eqb
  end%list.

Definition ternary_semantics {x y z r} (prim: TernaryPrim x y z r)
  : denote_type x -> denote_type y -> denote_type z -> denote_type r :=
  match prim in TernaryPrim x y z r return denote_type x -> denote_type y -> denote_type z -> denote_type r with
  | TernVecReplace => fun ls i x => replace (N.to_nat i) x ls
  end.

