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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Export MonadNotation.

Require Vector.
From Coq Require Import Bool.Bvector.
From Coq Require Import Fin.
From Coq Require Import NArith.Ndigits.
From Coq Require Import ZArith.

From Coq Require Import Lia.

Require Import Cava.Cava.
From Cava Require Import Kind.
From Cava Require Import Signal.
Require Import Cava.Monad.CavaClass.

(******************************************************************************)
(* A boolean combinational logic interpretation for the Cava class            *)
(******************************************************************************)

Definition notBool (i: bool) : ident bool :=
  ret (negb i).

Definition andBool '(a, b) : ident bool :=
  ret (a && b).

Definition nandBool (i: bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (a && b)).

Definition orBool (i: bool * bool) : ident bool :=
  let (a, b) := i in ret (a || b).

Definition norBool (i: bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (a || b)).

Definition xorBool (i: bool * bool) : ident bool :=
  let (a, b) := i in ret (xorb a b).

Definition xnorBool (i : bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (xorb a b)).

Definition lut1Bool (f: bool -> bool) (i: bool) : ident bool := ret (f i).

Definition lut2Bool (f: bool -> bool -> bool) (i: bool * bool) : ident bool :=
  ret (f (fst i) (snd i)).

Definition lut3Bool (f: bool -> bool -> bool -> bool) (i: bool * bool * bool) :
                    ident bool :=
  let '(i0, i1, i2) := i in
  ret (f i0 i1 i2).

Definition lut4Bool (f: bool -> bool -> bool -> bool -> bool)
                    (i: bool * bool * bool * bool) : ident bool :=
  let '(i0, i1, i2, i3) := i in
  ret (f i0 i1 i2 i3).

Definition lut5Bool (f: bool -> bool -> bool -> bool -> bool -> bool)
                    (i: bool * bool * bool * bool * bool) : ident bool :=
  let '(i0, i1, i2, i3, i4) := i in
  ret (f i0 i1 i2 i3 i4).

Definition lut6Bool (f: bool -> bool -> bool -> bool -> bool -> bool -> bool)
                    (i: bool * bool * bool * bool * bool * bool) : ident bool :=
  let '(i0, i1, i2, i3, i4, i5) := i in
  ret (f i0 i1 i2 i3 i4 i5).

Definition xorcyBool (i: bool * bool) : ident bool :=
  let (ci, li) := i in ret (xorb ci li).

Definition muxcyBool (s : bool) (ci : bool) (di : bool) : ident bool :=
  ret (match s with
       | false => di
       | true => ci
       end).

Fixpoint defaultKindBool (k: Kind) : smashTy bool k :=
  match k return smashTy bool k  with
  | Void => UndefinedSignal
  | Bit => false
  | BitVec k2 sz => Vector.const (defaultKindBool k2) sz
  | ExternalType _ => UninterpretedSignal "XXX"
  end.

Definition indexAtBool {k: Kind}
                       {sz isz: nat}
                       (i : Vector.t (smashTy bool k) sz)
                       (sel : Bvector isz) : smashTy bool k :=
  let selN := Bv2N sel in
  match lt_dec (N.to_nat selN) sz with
  | left H => @Vector.nth_order _ _ i (N.to_nat selN) H
  | right _ => defaultKindBool k
  end.

Definition indexConstBool {k: Kind} {sz: nat}
                          (i : Vector.t (smashTy bool k) sz)
                          (sel : nat) : smashTy bool k :=
  match lt_dec sel sz with
  | left H => @Vector.nth_order _ _ i sel H
  | right _ => defaultKindBool k
  end.

Definition sliceBool {k: Kind}
                     {sz: nat}
                     (startAt len : nat)
                     (v: Vector.t (smashTy bool k) sz)
                     (H: startAt + len <= sz) :
                     Vector.t (smashTy bool k) len :=
  sliceVector v startAt len H.

Definition unsignedAddBool {m n : nat}
                           (av : Bvector m) (bv : Bvector n) :
                           ident (Bvector (1 + max m n)) :=
  let a := Bv2N av in
  let b := Bv2N bv in
  let sumSize := 1 + max m n in
  let sum := (a + b)%N in
  ret (N2Bv_sized sumSize sum).

Definition greaterThanOrEqualBool {m n : nat}
                                  (av : Bvector m) (bv : Bvector n) :
                                  ident bool :=
  let a := N.to_nat (Bv2N av) in
  let b := N.to_nat (Bv2N bv) in
  ret (b <=? a).

Definition bufBool (i : bool) : ident bool :=
  ret i.

Definition loopBitBool (A B : Type) (f : A * bool -> ident (B * bool)) (a : A) : ident B :=
  '(b, _) <- f (a, false) ;;
  ret b.

(******************************************************************************)
(* Instantiate the Cava class for a boolean combinational logic               *)
(* interpretation.                                                            *)
(******************************************************************************)

Program Instance CavaBool : Cava ident bool :=
  { zero := ret false;
    one := ret true;
    delayBit i := ret i; (* Dummy definition for delayBit for now. *)
    loopBit a b := loopBitBool a b;
    inv := notBool;
    and2 := andBool;
    nand2 := nandBool;
    or2 := orBool;
    nor2 := norBool;
    xor2 := xorBool;
    xnor2 := xnorBool;
    buf_gate := bufBool;
    lut1 := lut1Bool;
    lut2 := lut2Bool;
    lut3 := lut3Bool;
    lut4 := lut4Bool;
    lut5 := lut5Bool;
    lut6 := lut6Bool;
    xorcy := xorcyBool;
    muxcy := muxcyBool;
    indexAt k sz isz := @indexAtBool k sz isz;
    indexBitAt sz isz := @indexAtBool Bit sz isz;
    indexConst k sz := @indexConstBool k sz;
    indexBitConst sz := @indexConstBool Bit sz;
    slice k sz := @sliceBool k sz;
    unsignedAdd m n := @unsignedAddBool m n;
    greaterThanOrEqual m n := @greaterThanOrEqualBool m n;
}.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition combinational {a} (circuit : ident a) : a := unIdent circuit.
