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


Require Import Coq.Lists.List.
Import ListNotations.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Export MonadNotation.

Require Import Coq.Bool.Bvector.
Require Import Coq.NArith.Ndigits.
Require Import Coq.ZArith.ZArith.

Require Import Cava.Cava.
Require Import Cava.Signal.
Require Import Cava.Acorn.CavaClass.

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

Definition pairSelBool {t : SignalType}
                       (sel : bool) (v : combType t * combType t) :=
  if sel then snd v else fst v.

Definition indexAtBool {t: SignalType}
                       {sz isz: nat}
                       (i : Vector.t (combType t) sz)
                       (sel : Bvector isz) : combType t :=
  nth_default (@defaultCombValue t) (N.to_nat (Bv2N sel)) i.

Definition indexConstBool {t: SignalType} {sz: nat}
                          (i : Vector.t (combType t) sz)
                          (sel : nat) : combType t :=
  nth_default (@defaultCombValue t) sel i.

Definition sliceBool {t: SignalType}
                     {sz: nat}
                     (startAt len : nat)
                     (v: Vector.t (combType t) sz)
                     (H: startAt + len <= sz) :
                     Vector.t (combType t) len :=
  sliceVector v startAt len H.

Definition bufBool (i : bool) : ident bool :=
  ret i.

Definition loopBool (A B C : SignalType)
                    (f : combType A * combType C -> ident (combType B * combType C))
                    (a : combType A) : ident (combType B) :=
  '(b, _) <- f (a, @defaultCombValue C) ;;
  ret b.

(******************************************************************************)
(* Instantiate the Cava class for a boolean combinational logic               *)
(* interpretation.                                                            *)
(******************************************************************************)

 Instance CombinationalSemantics : Cava combType :=
  { cava := ident;
    constant b := b;
    zero := ret false;
    one := ret true;
    defaultSignal t := @defaultCombValue t;
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
    unpair _ _ v := v;
    mkpair _ _ v1 v2 := (v1, v2);
    peel _ _ v := v;
    unpeel _ _ v := v;
    pairSel t sel v := pairSelBool sel v;
    indexAt t sz isz := @indexAtBool t sz isz;
    indexConst t sz := @indexConstBool t sz;
    slice t sz := @sliceBool t sz;
    unsignedAdd m n := fun x  y => ret (@unsignedAddBool m n x y);
    unsignedMult m n := fun x y => ret (@unsignedMultBool m n x y);
    greaterThanOrEqual m n := fun x y => ret (@greaterThanOrEqualBool m n x y);
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefault (map port_type (circuitOutputs intf)));
}.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition combinational {a} (circuit : cava a) : a := unIdent circuit.
