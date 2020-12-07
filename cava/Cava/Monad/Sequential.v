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


From Coq Require Import Lists.List.
Import ListNotations.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Structures.Traversable.
Export MonadNotation.

From Coq Require Import Bool.Bvector.

Require Import Cava.Cava.
From Cava Require Import Signal.
Require Import Cava.Monad.CavaClass.
Require Import Cava.Monad.CombinationalMonad.

(******************************************************************************)
(* Loop combinator for feedback with delay.                                   *)
(******************************************************************************)

(*
loopSeq' takes a combinational circuit f which has a pair of inputs which
represent the current input of type A and current state of type C. This circuit
returns a pair which represents the computed output of type B and next state
value of type C. The list of input values for each clock tick are provided
by the a parameter and the current state value is provided by the feedback
parameter. The result of the loopSeq' is a list in the identity monad that
represented the list of computed values at each tick.
*)

Fixpoint loopSeq' {A B C : SignalType}
                  (f : seqType A * seqType C -> ident (seqType B * seqType C))
                  (a : seqType A) (feedback: seqType C)
  : ident (seqType B) :=
  match a with
  | [] => ret []
  | x :: xs =>
    '(yL, nextState) <- f ([x], feedback) ;; (* One step of f. *)
    let y := hd defaultSignal yL in
    ys <- loopSeq' f xs nextState ;; (* remaining steps of f *)
    ret (y :: ys)
  end.

(*
The loopSeq combinator takes a combinational circuit f which maps a pair
representing the current input and current state to another pair
representing the computed output and next state value. This function is used
to compute the sequential behaviour of a circuit which uses f to iterate over
the a inputs, using a default value for the initial state.
*)

Definition loopSeq {A B C : SignalType}
                   (f : seqType A * seqType C -> ident (seqType B * seqType C))
                   (a : seqType A)
                   : ident (seqType B) :=
  loopSeq' f a [defaultCombValue C].

(******************************************************************************)
(* A boolean sequential logic interpretation for the Cava class               *)
(******************************************************************************)

Definition notBoolList (i : list bool) : ident (list bool) :=
  mapT notBool i.

Definition andBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  mapT andBool (combine (fst i) (snd i)).

Definition nandBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  mapT nandBool (combine (fst i) (snd i)).

Definition orBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  mapT orBool (combine (fst i) (snd i)).

Definition norBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  mapT norBool (combine (fst i) (snd i)).

Definition xorBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  mapT xorBool (combine (fst i) (snd i)).

Definition xnorBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  mapT xnorBool (combine (fst i) (snd i)).

Definition lut1BoolList (f: bool -> bool) (i : list bool) : ident (list bool) :=
  ret (map f i).

Definition lut2BoolList (f: bool -> bool -> bool)
                        (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in f a b)
           (combine (fst i) (snd i))).

Definition lut3BoolList (f: bool -> bool -> bool -> bool)
                        (i : (list bool) * (list bool) * (list bool)) : ident (list bool) :=
  let '(aL, bL, cL) := i in
  ret (map (fun (i : bool * bool * bool) => let '(a, b, c) := i in f a b c)
           (combine (combine aL bL) cL)).

Definition lut4BoolList (f: bool -> bool -> bool -> bool -> bool)
                        (i : (list bool) * (list bool) * 
                             (list bool) * (list bool)) : ident (list bool) :=
  let '(aL, bL, cL, dL) := i in
  ret (map (fun (i : bool * bool * bool * bool) =>
            let '(a, b, c, d) := i in f a b c d)
           (combine (combine (combine aL bL) cL) dL)).

Definition lut5BoolList (f: bool -> bool -> bool -> bool -> bool -> bool)
                        (i : (list bool) * (list bool) * (list bool) *
                             (list bool) * (list bool)) : ident (list bool) :=
  let '(aL, bL, cL, dL, eL) := i in
  ret (map (fun (i : bool * bool * bool * bool * bool) =>
            let '(a, b, c, d, e) := i in f a b c d e)
           (combine (combine (combine (combine aL bL) cL) dL) eL)).

Definition lut6BoolList (fn: bool -> bool -> bool -> bool -> bool -> bool -> bool)
                        (i : (list bool) * (list bool) * (list bool) *
                             (list bool) * (list bool) * (list bool)) :
                        ident (list bool) :=
  let '(aL, bL, cL, dL, eL, fL) := i in
  ret (map (fun (i : bool * bool * bool * bool * bool * bool) =>
            let '(a, b, c, d, e, f) := i in fn a b c d e f)
           (combine (combine (combine (combine (combine aL bL) cL) dL) eL) fL)).

Definition xorcyBoolList := xorBoolList.

Definition muxcyBoolList (s : list bool) (ci : list bool) (di : list bool)  : ident (list bool) :=
  let dici := combine di ci in
  let s_dici := combine s dici in
  ret (map (fun (i : bool * (bool * bool)) =>
     let '(s, (ci, di)) := i in
     match s with
       | false => di
       | true => ci
     end) s_dici).

Definition indexAtBoolList {t: SignalType}
                       {sz isz: nat}
                       (i : list (Vector.t (combType t) sz))
                       (sel : list (Bvector isz)) : list (combType t) :=
  map (fun '(i, sel) => indexAtBool i sel) (combine i sel).

Definition indexConstBoolList {t: SignalType} {sz: nat}
                              (i : list (Vector.t (combType t) sz))
                              (sel : nat) : list (combType t) :=
  map (fun i => indexConstBool i sel) i.

Definition sliceBoolList {t: SignalType}
                         {sz: nat}
                         (startAt len : nat)
                         (v: list (Vector.t (combType t) sz))
                         (H: startAt + len <= sz) :
                         list (Vector.t (combType t) len) :=
  map (fun v => sliceBool startAt len v H) v.

Definition peelVecList {t: SignalType} {s: nat}
                       (v: list (Vector.t (combType t) s))
                       : Vector.t (list (combType t)) s :=
 Vector.map (fun i => map (fun j => indexConstBool j i) v) (vseq 0 s).

Definition unpeelVecList' {t: SignalType} {s: nat}
                         (v: Vector.t (list (combType t)) s)
                         (l: nat)
                         : list (Vector.t (combType t) s) :=
  map (fun ni => Vector.map (fun vi => nth ni vi (defaultCombValue t)) v) (seq 0 l).

Local Open Scope vector_scope.

Definition unpeelVecList {t: SignalType} {s: nat}
                         (v: Vector.t (list (combType t)) s)
                         : list (Vector.t (combType t) s) :=
  match s, v with
  | O, _ => []
  | S n, x::xs => unpeelVecList' v (length x)
  | S _, [] => []
  end.

Local Open Scope list_scope.

Definition unsignedAddBoolList {m n : nat}
                               (av : list (Bvector m)) (bv : list (Bvector n)) :
                               ident (list (Bvector (1 + max m n))) :=
  mapT (fun '(a, b) => unsignedAddBool a b) (combine av bv).

Definition unsignedMultBoolList {m n : nat}
                                (av : list (Bvector m)) (bv : list (Bvector n)) :
                                ident (list (Bvector (m + n))) :=
  mapT (fun '(a, b) => unsignedMultBool a b) (combine av bv).

Definition greaterThanOrEqualBoolList {m n : nat}
                                      (av : list (Bvector m)) (bv : list (Bvector n)) :
                                      ident (list bool) :=
  mapT (fun '(a, b) => greaterThanOrEqualBool a b) (combine av bv).

Definition bufBoolList (i : list bool) : ident (list bool) :=
  ret i.

(******************************************************************************)
(* Instantiate the Cava class for a boolean sequential logic                  *)
(* interpretation.                                                            *)
(******************************************************************************)

 Instance SequentialCombSemantics : Cava seqType :=
  { cava := ident;
    zero := ret [false];
    one := ret [true];
    defaultSignal t := @defaultSeqValue t;
    inv := notBoolList;
    and2 := andBoolList;
    nand2 := nandBoolList;
    or2 := orBoolList;
    nor2 := norBoolList;
    xor2 := xorBoolList;
    xnor2 := xnorBoolList;
    buf_gate := bufBoolList;
    lut1 := lut1BoolList;
    lut2 := lut2BoolList;
    lut3 := lut3BoolList;
    lut4 := lut4BoolList;
    lut5 := lut5BoolList;
    lut6 := lut6BoolList;
    xorcy := xorcyBoolList;
    muxcy := muxcyBoolList;
    peel _ _ v := peelVecList v;
    unpeel _ _ v := unpeelVecList v;
    indexAt t sz isz := @indexAtBoolList t sz isz;
    indexConst t sz := @indexConstBoolList t sz;
    slice t sz := @sliceBoolList t sz;
    unsignedAdd m n := @unsignedAddBoolList m n;
    unsignedMult m n := @unsignedMultBoolList m n;
    greaterThanOrEqual m n := @greaterThanOrEqualBoolList m n;
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefaultS (map port_type (circuitOutputs intf)));
    delay k i := ret (@defaultCombValue k :: i);
   loop _ _ _ := loopSeq;
}.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition sequential {a} (circuit : cava a) : a := unIdent circuit.