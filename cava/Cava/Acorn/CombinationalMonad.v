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


Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Export MonadNotation.

Require Import Coq.Bool.Bvector.
Require Import Coq.NArith.Ndigits.
Require Import Coq.ZArith.ZArith.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Acorn.CavaClass.

(******************************************************************************)
(* A boolean combinational logic interpretation for the Cava class            *)
(******************************************************************************)

Definition nandb b1 b2 : bool := negb (andb b1 b2).
Definition norb b1 b2 : bool := negb (orb b1 b2).
Definition xnorb b1 b2 : bool := negb (xorb b1 b2).

Definition lastSignal {A} (l : seqType A) : combType A := last l (defaultCombValue A).

(* If one signal sequence is shorter than the other, repeat the last signal of
   the shorter sequence until lengths match, then combine the lists. *)
Definition pad_combine {A B : SignalType}
           (a : seqType A) (b : seqType B) : seqType (Pair A B) :=
  combine (extend a (lastSignal a) (length b))
          (extend b (lastSignal b) (length a)).

Definition lift1 {A B} (f : combType A -> combType B) (a : seqType A)
  : ident (seqType B) :=
  ret (map f a).

Definition liftP {A B C} (f : combType A * combType B -> combType C)
           (ab : seqType A * seqType B)
  : seqType C :=
  let (a, b) := ab in
  map f (pad_combine a b).

Definition lift2 {A B C} (f : combType A -> combType B -> combType C)
           (a : seqType A) (b : seqType B)
  : ident (seqType C) :=
  ret (map (fun ab => f (fst ab) (snd ab)) (pad_combine a b)).

Definition lift3 {A B C D}
           (f : combType A -> combType B -> combType C -> combType D)
           (a : seqType A) (b : seqType B) (c : seqType C)
  : ident (seqType D) :=
  ret (map (fun abc =>
              f (fst (fst abc)) (snd (fst abc)) (snd abc))
           (pad_combine (pad_combine a b) c)).

Definition lift4 {A B C D E}
           (f : combType A -> combType B -> combType C -> combType D -> combType E)
           (a : seqType A) (b : seqType B) (c : seqType C) (d : seqType D)
  : ident (seqType E) :=
  ret (map (fun abcd =>
              f (fst (fst (fst abcd))) (snd (fst (fst abcd))) (snd (fst abcd))
                (snd abcd))
           (pad_combine (pad_combine (pad_combine a b) c) d)).

Definition lift5 {A B C D E G}
           (f : combType A -> combType B -> combType C -> combType D -> combType E
                -> combType G)
           (a : seqType A) (b : seqType B) (c : seqType C) (d : seqType D)
           (e : seqType E) : ident (seqType G) :=
  ret (map (fun abcde =>
              f (fst (fst (fst (fst abcde)))) (snd (fst (fst (fst abcde))))
                (snd (fst (fst abcde))) (snd (fst abcde)) (snd abcde))
           (pad_combine (pad_combine (pad_combine (pad_combine a b) c) d) e)).

Definition lift6 {A B C D E G H}
           (f : combType A -> combType B -> combType C -> combType D -> combType E
                -> combType G -> combType H)
           (a : seqType A) (b : seqType B) (c : seqType C) (d : seqType D)
           (e : seqType E) (g : seqType G) : ident (seqType H) :=
  ret (map (fun abcdeg =>
              f (fst (fst (fst (fst (fst abcdeg)))))
                (snd (fst (fst (fst (fst abcdeg)))))
                (snd (fst (fst (fst abcdeg)))) (snd (fst (fst abcdeg)))
                (snd (fst abcdeg)) (snd abcdeg))
           (pad_combine
              (pad_combine (pad_combine (pad_combine (pad_combine a b) c) d) e) g)).

Definition pairSelBool {t : SignalType}
                       (sel : bool) (v : combType t * combType t) :=
  if sel then snd v else fst v.

Definition indexConstBoolList {t: SignalType} {sz: nat}
           (v : seqType (Vec t sz)) (sel : nat)
  : seqType t :=
  map (nth_default (defaultCombValue t) sel) v.

Definition indexAtBoolList {t: SignalType} {sz isz: nat}
           (v : seqType (Vec t sz)) (sel : seqType (Vec Bit isz))
  : seqType t :=
  map (fun '(sel, v) =>
         nth_default (defaultCombValue t) (N.to_nat (Bv2N sel)) v)
      (pad_combine sel v).

Definition peelVecList {t: SignalType} {s: nat}
                       (v: list (Vector.t (combType t) s))
                       : Vector.t (list (combType t)) s :=
 Vector.map (indexConstBoolList v) (vseq 0 s).

Definition unpeelVecList {t: SignalType} {s: nat}
                         (v: Vector.t (list (combType t)) s)
                         : list (Vector.t (combType t) s) :=
  let max_length := Vector.fold_left Nat.max 0 (Vector.map (@length _) v) in
  map (fun ni => Vector.map (fun vi => nth ni vi (defaultCombValue t)) v)
      (seq 0 max_length).

Definition sliceBoolList {t: SignalType}
                         {sz: nat}
                         (startAt len : nat)
                         (v: list (Vector.t (combType t) sz))
                         (H: startAt + len <= sz) :
                         list (Vector.t (combType t) len) :=
  map (fun v => sliceVector v startAt len H) v.

Local Notation lift1Bool := (@lift1 Bit Bit).
Local Notation lift2Bool := (@lift2 Bit Bit Bit).
Local Notation lift3Bool := (@lift3 Bit Bit Bit Bit).
Local Notation lift4Bool := (@lift4 Bit Bit Bit Bit Bit).
Local Notation lift5Bool := (@lift5 Bit Bit Bit Bit Bit Bit).
Local Notation lift6Bool := (@lift6 Bit Bit Bit Bit Bit Bit Bit).

(******************************************************************************)
(* Instantiate the Cava class for a boolean combinational logic               *)
(* interpretation.                                                            *)
(******************************************************************************)

Instance CombinationalSemantics : Cava seqType :=
  { cava := ident;
    monad := Monad_ident;
    constant := fun x => [x];
    defaultSignal t := [];
    inv := lift1Bool negb;
    and2 :=  fun '(x,y) => lift2Bool andb x y;
    nand2 := fun '(x,y) => lift2Bool nandb x y;
    or2 :=   fun '(x,y) => lift2Bool orb x y;
    nor2 :=  fun '(x,y) => lift2Bool norb x y;
    xor2 :=  fun '(x,y) => lift2Bool xorb x y;
    xnor2 := fun '(x,y) => lift2Bool xnorb x y;
    buf_gate := ret;
    lut1 := lift1Bool;
    lut2 := fun f '(a,b) => lift2Bool f a b;
    lut3 := fun f '(a,b,c) => lift3Bool f a b c;
    lut4 := fun f '(a,b,c,d) => lift4Bool f a b c d;
    lut5 := fun f '(a,b,c,d,e) => lift5Bool f a b c d e;
    lut6 := fun f '(a,b,c,d,e,g) => lift6Bool f a b c d e g;
    xorcy := fun '(x,y) => lift2Bool xorb x y;
    muxcy := lift3Bool (fun sel x y => if sel then x else y);
    unpair _ _ v := split v;
    mkpair _ _ v1 v2 := pad_combine v1 v2;
    peel _ _ v := peelVecList v;
    unpeel _ _ v := unpeelVecList v;
    indexAt t sz isz := @indexAtBoolList t sz isz;
    indexConst t sz := @indexConstBoolList t sz;
    slice t sz := @sliceBoolList t sz;
    unsignedAdd m n := @liftP (Vec Bit m) (Vec Bit n) (Vec Bit (1 + max m n)) (@unsignedAddBool m n);
    unsignedMult m n := @liftP (Vec Bit _) (Vec Bit _) (Vec Bit _)
                               (@unsignedMultBool m n);
    greaterThanOrEqual m n := @liftP (Vec Bit _) (Vec Bit _) Bit
                                     (@greaterThanOrEqualBool m n);
    localSignal _ v := ret v;
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefaultS (map port_type (circuitOutputs intf)));
}.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition combinational {a} (circuit : cava a) : a := unIdent circuit.
