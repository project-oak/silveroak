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
From Coq Require Import Strings.Ascii Strings.String.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Traversable.
Export MonadNotation.

Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bvector.
Import VectorNotations.

From Coq Require Import Fin.
From Coq Require Import NArith.Ndigits.
From Coq Require Import ZArith.ZArith.

From Coq Require Import micromega.Lia.

Require Import Cava.Cava.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.TimedMonad.
Require Import Cava.Acorn.CombinationalMonad.

(******************************************************************************)
(* Delay combinator.                                                          *)
(******************************************************************************)

Definition delay {A} (x : timed (combType A)) : timed (combType A) :=
  fun t =>
    match t with
    | 0 => defaultCombValue A
    | S t' => x t'
    end.

(******************************************************************************)
(* Loop combinator for feedback with delay.                                   *)
(******************************************************************************)

Definition loopSeqF' {A B : SignalType}
         (f : combType A * combType B -> combType B)
         (a : timed (combType A)) : timed (combType B) :=
  timedFold (fun b a => f (a, b)) (defaultCombValue B) a.

Definition loopSeqF {A B : SignalType}
         (f : combType A * combType B -> timed (combType B))
         (a : timed (combType A)) : timed (combType B) :=
  loopSeqF' (fun ac => f ac 0) a.

(******************************************************************************)
(* A boolean sequential logic interpretation for the Cava class               *)
(******************************************************************************)

Definition unopF (f : bool -> bool) (i : combType Bit) : timed (combType Bit) :=
  ret (f i).

Definition binopF (f : bool -> bool -> bool) (i : combType Bit * combType Bit) : timed (combType Bit) :=
  ret (f (fst i) (snd i)).

Definition lut1BoolF (f: bool -> bool) (i : bool) : timed bool :=
  ret (f i).

Definition lut2BoolF (f: bool -> bool -> bool) (i : bool * bool) : timed bool :=
  let '(i0, i1) := i in
  ret (f i0 i1).

Definition lut3BoolF (f: bool -> bool -> bool -> bool) (i : bool * bool * bool) : timed bool :=
  let '(i0, i1, i2) := i in
  ret (f i0 i1 i2).

Definition lut4BoolF (f: bool -> bool -> bool -> bool -> bool) (i : bool * bool * bool * bool) : timed bool :=
  let '(i0, i1, i2, i3) := i in
  ret (f i0 i1 i2 i3).

Definition lut5BoolF (f: bool -> bool -> bool -> bool -> bool -> bool)
           (i : bool * bool * bool * bool * bool) : timed bool :=
  let '(i0, i1, i2, i3, i4) := i in
  ret (f i0 i1 i2 i3 i4).

Definition lut6BoolF (f: bool -> bool -> bool -> bool -> bool -> bool -> bool)
           (i : bool * bool * bool * bool * bool * bool) : timed bool :=
  let '(i0, i1, i2, i3, i4, i5) := i in
  ret (f i0 i1 i2 i3 i4 i5).

Definition muxcyBoolF (s ci di : bool) : timed bool :=
  ret (if s then ci else di).

Definition indexConstBoolF {t sz} (v : combType (Vec t sz)) (sel : nat) :=
  nth_default (defaultCombValue _) sel v.

Definition indexAtBoolF {t sz isz}
           (v : combType (Vec t sz)) (sel : combType (Vec Bit isz)) :=
  nth_default (defaultCombValue _) (N.to_nat (Bv2N sel)) v.

Definition unsignedAddBoolF {m n : nat} (av_bv : Bvector m * Bvector n)
  : Bvector (1 + max m n) :=
   unsignedAddBool av_bv.

Definition unsignedMultBoolF {m n : nat} (av_bv : Bvector m * Bvector n)
  : Bvector (m + n) :=
  unsignedMultBool av_bv.

Definition greaterThanOrEqualBoolF {m n : nat} (av_bv : Bvector m * Bvector n)
  : bool :=
  greaterThanOrEqualBool av_bv.


Definition blackBoxF (intf : CircuitInterface)
  : timed (tupleInterface combType (List.map port_type (circuitOutputs intf))) :=
  ret (tupleInterfaceDefault (map port_type (circuitOutputs intf))).


(******************************************************************************)
(* Instantiate the Cava class for a boolean sequential logic                  *)
(* interpretation.                                                            *)
(******************************************************************************)

(*

TODO: Work out if there is a sensible way to reintroduce TimedCombSemantics.

 Instance TimedCombSemantics : Cava combType :=
  { cava := timed;
    constant b := b;
    defaultSignal t := defaultCombValue t;
    inv := unopF negb;
    and2 := binopF andb;
    nand2 := binopF (fun a b => negb (andb a b));
    or2 := binopF orb;
    nor2 := binopF (fun a b => negb (orb a b));
    xor2 := binopF xorb;
    xnor2 := binopF (fun a b => negb (xorb a b));
    buf_gate := @ret timed Monad_timed bool;
    lut1 := lut1BoolF;
    lut2 := lut2BoolF;
    lut3 := lut3BoolF;
    lut4 := lut4BoolF;
    lut5 := lut5BoolF;
    lut6 := lut6BoolF;
    xorcy := binopF xorb;
    muxcy := muxcyBoolF;
    mkpair _ _ v1 v2 := (v1, v2);
    unpair _ _ v := v;
    peel _ _ v := v;
    unpeel _ _ v := v;
    indexAt t sz isz := @indexAtBoolF t sz isz;
    indexConst t sz := @indexConstBoolF t sz;
    slice t sz startAt len v H := sliceVector v startAt len H;
    unsignedAdd m n := @unsignedAddBoolF m n;
    unsignedMult m n := @unsignedMultBoolF m n;
    greaterThanOrEqual m n := @greaterThanOrEqualBoolF m n;
    instantiate _ circuit := circuit;
    blackBox intf _ := blackBoxF intf;
  }.

 Instance TimedSeqSemantics : CavaSeqMonad TimedCombSemantics :=
   { delaym k i := delay i;
     loopDelaySm A B := @loopSeqF A B;
   }.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result at the given timestep.                       *)
(******************************************************************************)

Definition sequentialF {a} (circuit : cava a) (t : nat) : a := circuit t.

*)