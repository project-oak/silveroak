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

(* Primitives will require both semantic and netlist implementations *)
Inductive UnaryPrim : type -> type -> Type :=
| UnVecSlice: forall {t n} (start len: nat), UnaryPrim (Vec t n) (Vec t len)

| UnVecRotateRight: forall {t n}, nat -> UnaryPrim (Vec t n) (Vec t n)
| UnVecShiftRight: forall {t n}, nat -> UnaryPrim (Vec t n) (Vec t n)

| UnVecToTuple: forall {t n}, UnaryPrim (Vec t n) (ntuple t n)
.

Inductive BinaryPrim : type -> type -> type -> Type :=
| BinBitAnd: BinaryPrim Bit Bit Bit
| BinBitOr: BinaryPrim Bit Bit Bit

| BinBitVecGte: forall {n}, BinaryPrim (BitVec n) (BitVec n) Bit

| BinVecIndex: forall {t n i}, BinaryPrim (Vec t n) (BitVec i) t
| BinVecCons: forall {t n}, BinaryPrim t (Vec t n) t

(* drop leftmost element and push one element in right side, e.g. shifting left *)
| BinVecShiftInRight: forall {t n}, BinaryPrim (Vec t n) t (Vec t n)
.

Inductive TernaryPrim : type -> type -> type -> type -> Type :=
| TernVecReplace: forall {t n i}, TernaryPrim (Vec t n) (BitVec i) t t
.

Section RefinedLists.
  Definition drop {A n} (start len: nat)
      (ls: {l : list A | Datatypes.length l = n}):
      {l : list A | Datatypes.length l = len} :=
    let (ls', Hlen) := ls in
    drop

  Definition slice {A n} (start len: nat)
      (ls: {l : list A | Datatypes.length l = n}):
      {l : list A | Datatypes.length l = len} :=
    let (ls', Hlen) := ls in
    drop
End.

Definition unary_semantics {x r} (prim: UnaryPrim x r)
  : denote_type x -> denote_type r :=
  match prim in UnaryPrim x r return denote_type x -> denote_type r with
  | @UnVecSlice t _ start len =>
    fun x =>
  | UnVecRotateRight n =>
    fun x => x
  | UnVecShiftRight n =>
    fun x => x
  | UnVecToTuple =>
    fun x => x
  end.
    (* match t with *)

