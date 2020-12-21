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
(* Combinational denotion of the SignalType and default values.               *)
(******************************************************************************)

Fixpoint combType (t: SignalType) : Type :=
  match t with
  | Void => unit
  | Bit => bool
  | Vec vt sz => Vector.t (combType vt) sz
  | Pair t1 t2 => (combType t1 * combType t2)%type
  | ExternalType _ => unit (* No semantics for combinational interpretation. *)
  end.

Fixpoint defaultCombValue (t: SignalType) : combType t :=
  match t  with
  | Void => tt
  | Bit => false
  | Vec t2 sz => Vector.const (defaultCombValue t2) sz
  | Pair t1 t2 => (defaultCombValue t1, defaultCombValue t2)
  | ExternalType _ => tt
  end.

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
                       (v : combType t * combType t) (sel : bool) :=
  if sel then snd v else fst v.

Definition indexAtBool {t: SignalType}
                       {sz isz: nat}
                       (i : Vector.t (combType t) sz)
                       (sel : Bvector isz) : combType t :=
  let selN := Bv2N sel in
  match lt_dec (N.to_nat selN) sz with
  | left H => @Vector.nth_order _ _ i (N.to_nat selN) H
  | right _ => defaultCombValue t
  end.

Definition indexConstBool {t: SignalType} {sz: nat}
                          (i : Vector.t (combType t) sz)
                          (sel : nat) : combType t :=
  match lt_dec sel sz with
  | left H => @Vector.nth_order _ _ i sel H
  | right _ => defaultCombValue t
  end.

Definition sliceBool {t: SignalType}
                     {sz: nat}
                     (startAt len : nat)
                     (v: Vector.t (combType t) sz)
                     (H: startAt + len <= sz) :
                     Vector.t (combType t) len :=
  sliceVector v startAt len H.

Definition unsignedAddBool {m n : nat}
                           (av : Bvector m) (bv : Bvector n) :
                           ident (Bvector (1 + max m n)) :=
  let a := Bv2N av in
  let b := Bv2N bv in
  let sumSize := 1 + max m n in
  let sum := (a + b)%N in
  ret (N2Bv_sized sumSize sum).

Definition unsignedMultBool {m n : nat}
                           (av : Bvector m) (bv : Bvector n) :
                           ident (Bvector (m + n)) :=
  let a := Bv2N av in
  let b := Bv2N bv in
  let product := (a * b)%N in
  ret (N2Bv_sized (m + n) product).

Definition greaterThanOrEqualBool {m n : nat}
                                  (av : Bvector m) (bv : Bvector n) :
                                  ident bool :=
  let a := N.to_nat (Bv2N av) in
  let b := N.to_nat (Bv2N bv) in
  ret (b <=? a).

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
    pairSel t v sel := pairSelBool v sel;
    indexAt t sz isz := @indexAtBool t sz isz;
    indexConst t sz := @indexConstBool t sz;
    slice t sz := @sliceBool t sz;
    unsignedAdd m n := @unsignedAddBool m n;
    unsignedMult m n := @unsignedMultBool m n;
    greaterThanOrEqual m n := @greaterThanOrEqualBool m n;
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefault (map port_type (circuitOutputs intf)));
}.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition combinational {a} (circuit : cava a) : a := unIdent circuit.
