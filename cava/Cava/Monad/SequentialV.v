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
From Cava Require Import Kind.
From Cava Require Import Signal.
Require Import Cava.Monad.CavaClass.
Require Import Cava.Monad.CombinationalMonad.

Local Open Scope vector_scope.

(* stepOnce is a helper function that takes a circuit running for > 1 ticks and
   runs it for only one tick. *)
Definition stepOnce {A B C : SignalType} {ticks : nat}
           (f : seqVType (S ticks) A * seqVType (S ticks) C
                -> ident (seqVType (S ticks) B * seqVType (S ticks) C))
           (input : seqVType 1 A * seqVType 1 C)
  : ident (seqVType 1 B * seqVType 1 C) :=
  let a := Vector.hd (fst input) in
  let c := Vector.hd (snd input) in
  '(b, c) <- f (a :: const (defaultCombValue A) ticks,
               c :: const (defaultCombValue C) ticks) ;;
  ret ([Vector.hd b], [Vector.hd c]).

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

Fixpoint loopSeqV' {A B C : SignalType}
                   (ticks: nat)
                   (f : seqVType 1 A * seqVType 1 C -> ident (seqVType 1 B * seqVType 1 C))
                   {struct ticks}
  : seqVType ticks A -> seqVType 1 C -> ident (seqVType ticks B) :=
  match ticks as ticks0 return seqVType ticks0 A -> _ -> ident (seqVType ticks0 B) with
  | O => fun _ _ => ret []
  | S ticks' =>
    fun a feedback =>
      let x := Vector.hd a in
      let xs := Vector.tl a in
      '(yL, nextState) <- f ([x], feedback) ;; (* One step of f. *)
      let y := Vector.hd yL in
      ys <- loopSeqV' ticks' f xs nextState ;; (* remaining steps of f *)
      ret (y :: ys)
  end.

(*
The loopSeq combinator takes a combinational circuit f which maps a pair
representing the current input and current state to another pair
representing the computed output and next state value. This function is used
to compute the sequential behaviour of a circuit which uses f to iterate over
the a inputs, using a default value for the initial state.
 *)

Definition loopSeqV {A B C : SignalType}
                    (ticks : nat)
  : (seqVType ticks A * seqVType ticks C
     -> ident (seqVType ticks B * seqVType ticks C))
    -> (seqVType ticks A) -> ident (seqVType ticks B) :=
  match ticks as ticks0 return
        (seqVType ticks0 A * seqVType ticks0 C
         -> ident (seqVType ticks0 B * seqVType ticks0 C))
        -> seqVType ticks0 A -> ident (seqVType ticks0 B)  with
  | O => fun _ _ => ret []
  | S ticks' =>
    fun f a =>
      loopSeqV' (S ticks') (stepOnce f)
                a [defaultCombValue C]
  end.

(******************************************************************************)
(* A boolean sequential logic interpretation for the Cava class               *)
(******************************************************************************)

Definition notBoolVec {ticks: nat} (i : Vector.t bool ticks)
                       : ident (Vector.t bool ticks) :=
  ret (Vector.map (fun a => negb a) i).

Definition binOpV {A B C : Type} (ticks: nat)
           (f: A -> B -> C)
           (i : Vector.t A ticks * Vector.t B ticks)
          : ident (Vector.t C ticks) :=
  ret (Vector.map (fun '(a, b) => f a b) (vcombine (fst i) (snd i))).

Definition lut1BoolVec (ticks: nat)
           (f: bool -> bool) (i : Vector.t bool ticks)
           : ident (Vector.t bool ticks) :=
  ret (Vector.map f i).

Definition lut2BoolVec (ticks: nat)
                       (f: bool -> bool -> bool)
                       (i : Vector.t bool ticks * Vector.t bool ticks)
                      : ident (Vector.t bool ticks) :=
  ret (Vector.map (fun (i : bool * bool) => let (a, b) := i in f a b)
           (vcombine (fst i) (snd i))).

Definition lut3BoolVec (ticks: nat)
                       (f: bool -> bool -> bool -> bool)
                       (i : Vector.t bool ticks * Vector.t bool ticks * Vector.t bool ticks)
                       : ident (Vector.t bool ticks) :=
  let '(aL, bL, cL) := i in
  ret (Vector.map (fun (i : bool * bool * bool) => let '(a, b, c) := i in f a b c)
                  (vcombine (vcombine aL bL) cL)).

Definition lut4BoolVec (ticks: nat)
                        (f: bool -> bool -> bool -> bool -> bool)
                        (i : Vector.t bool ticks  * Vector.t bool ticks * 
                             Vector.t bool ticks * Vector.t bool ticks)
                        : ident (Vector.t bool ticks) :=
  let '(aL, bL, cL, dL) := i in
  ret (Vector.map (fun (i : bool * bool * bool * bool) =>
            let '(a, b, c, d) := i in f a b c d)
           (vcombine (vcombine (vcombine aL bL) cL) dL)).

Definition lut5BoolVec (ticks: nat)
                       (f: bool -> bool -> bool -> bool -> bool -> bool)
                       (i : Vector.t bool ticks * Vector.t bool ticks * Vector.t bool ticks *
                            Vector.t bool ticks * Vector.t bool ticks)
                       : ident (Vector.t bool ticks) :=
  let '(aL, bL, cL, dL, eL) := i in
  ret (Vector.map (fun (i : bool * bool * bool * bool * bool) =>
            let '(a, b, c, d, e) := i in f a b c d e)
           (vcombine (vcombine (vcombine (vcombine aL bL) cL) dL) eL)).

Definition lut6BoolVec (ticks: nat)
                      (fn: bool -> bool -> bool -> bool -> bool -> bool -> bool)
                      (i : Vector.t bool ticks * Vector.t bool ticks * Vector.t bool ticks *
                           Vector.t bool ticks * Vector.t bool ticks * Vector.t bool ticks) :
                      ident (Vector.t bool ticks) :=
  let '(aL, bL, cL, dL, eL, fL) := i in
  ret (Vector.map (fun (i : bool * bool * bool * bool * bool * bool) =>
            let '(a, b, c, d, e, f) := i in fn a b c d e f)
           (vcombine (vcombine (vcombine (vcombine (vcombine aL bL) cL) dL) eL) fL)).

Definition muxcyBoolVec (ticks: nat)
                        (s :  Vector.t bool ticks)
                        (ci : Vector.t bool ticks)
                        (di : Vector.t bool ticks)
                        : ident ( Vector.t bool ticks) :=
  let dici := vcombine di ci in
  let s_dici := vcombine s dici in
  ret (Vector.map (fun (i : bool * (bool * bool)) =>
     let '(s, (ci, di)) := i in
     match s with
       | false => di
       | true => ci
     end) s_dici).

Definition indexAtBoolVec {t: SignalType}
                          {sz isz: nat}
                          (ticks: nat)
                          (i : Vector.t (Vector.t (combType t) sz) ticks)
                          (sel : Vector.t (Bvector isz) ticks)
                          : Vector.t (combType t) ticks :=
  Vector.map (fun '(i, sel) => indexAtBool i sel) (vcombine i sel).

Definition indexConstBoolVec {t: SignalType} {sz: nat}
                             (ticks: nat)
                             (i : Vector.t (Vector.t (combType t) sz) ticks)
                             (sel : nat)
                             : Vector.t (combType t) ticks :=
  Vector.map (fun i => indexConstBool i sel) i.

Definition sliceBoolVec {t: SignalType}
                        {sz: nat}
                        (ticks: nat)
                        (startAt len : nat)
                        (v: Vector.t (Vector.t (combType t) sz) ticks)
                        (H: startAt + len <= sz) :
                        Vector.t (Vector.t (combType t) len) ticks :=
  Vector.map (fun v => sliceBool startAt len v H) v.

Definition peelVecVec {t: SignalType} {s: nat}
                      (ticks: nat)
                      (v: Vector.t (Vector.t (combType t) s) ticks)
                      : Vector.t (Vector.t (combType t) ticks) s :=
 Vector.map (fun i => Vector.map (fun j => indexConstBool j i) v) (vseq 0 s).

Definition unpeelVecVec {t: SignalType} {s: nat}
                        (ticks: nat)
                        (v: Vector.t (Vector.t (combType t) ticks) s)
                        : Vector.t (Vector.t (combType t) s) ticks :=
  Vector.map (fun ni => Vector.map (fun vi => indexConstBool vi ni) v) (vseq 0 ticks).

Definition unsignedAddComb {m n : nat}
                           (av : Bvector m) (bv : Bvector n) :
                           Bvector (1 + max m n) :=
  let a := Bv2N av in
  let b := Bv2N bv in
  let sumSize := 1 + max m n in
  let sum := (a + b)%N in
  N2Bv_sized sumSize sum.

Definition unsignedAddBoolVec {m n : nat}
                              (ticks: nat)
                              (av : Vector.t (Bvector m) ticks)
                              (bv : Vector.t (Bvector n) ticks) :
                              ident (Vector.t (Bvector (1 + max m n)) ticks) :=
  binOpV ticks unsignedAddComb (av, bv).

Definition unsignedMultComb {m n : nat}
                            (av : Bvector m) (bv : Bvector n) :
                            Bvector (m + n) :=
  let a := Bv2N av in
  let b := Bv2N bv in
  let product := (a * b)%N in
  N2Bv_sized (m + n) product.

Definition unsignedMultBoolVec {m n : nat}
                               (ticks: nat)
                               (av : Vector.t (Bvector m) ticks)
                               (bv : Vector.t (Bvector n) ticks) :
                               ident (Vector.t (Bvector (m + n)) ticks) :=
  binOpV ticks unsignedMultComb (av, bv).

Definition greaterThanOrEqualComb {m n : nat}
                                  (av : Bvector m) (bv : Bvector n) :
                                  bool :=
  let a := N.to_nat (Bv2N av) in
  let b := N.to_nat (Bv2N bv) in
  b <=? a.

Definition greaterThanOrEqualBoolVec {m n : nat}
                                     (ticks: nat)
                                     (av : Vector.t (Bvector m) ticks)
                                     (bv : Vector.t (Bvector n) ticks) :
                                     ident (Bvector ticks) :=
  binOpV ticks greaterThanOrEqualComb (av, bv).

Definition bufBoolVec (ticks: nat)
           (i : Vector.t bool ticks) : ident (Vector.t bool ticks) :=
  ret i.

Definition delayV (ticks : nat) (t : SignalType) : seqVType ticks t -> ident (seqVType ticks t) :=
  match ticks as ticks0 return seqVType ticks0 t -> ident (seqVType ticks0 t) with
  | O => fun _ => ret []
  | S ticks' => fun i => ret (defaultCombValue t :: Vector.shiftout i)
  end.

(******************************************************************************)
(* Instantiate the Cava class for a boolean sequential logic                  *)
(* interpretation.                                                            *)
(******************************************************************************)

 Instance SequentialVectorCombSemantics {ticks: nat} : Cava (seqVType ticks) :=
  { cava := ident;
    zero := ret (Vector.const false ticks);
    one := ret (Vector.const true ticks);
    defaultSignal t := Vector.const (@defaultCombValue t) ticks;
    inv := notBoolVec;
    and2 := binOpV ticks andb;
    nand2 := binOpV ticks (fun a b => negb (a && b));
    or2 := binOpV ticks orb;
    nor2 := binOpV ticks (fun a b => negb (a || b));
    xor2 := binOpV ticks xorb;
    xnor2 := binOpV ticks (fun a b => negb (xorb a b));
    buf_gate := bufBoolVec ticks;
    lut1 := lut1BoolVec ticks;
    lut2 := lut2BoolVec ticks;
    lut3 := lut3BoolVec ticks;
    lut4 := lut4BoolVec ticks;
    lut5 := lut5BoolVec ticks;
    lut6 := lut6BoolVec ticks;
    xorcy := binOpV ticks xorb;
    muxcy := muxcyBoolVec ticks;
    peel _ _ v := peelVecVec ticks v;
    unpeel _ _ v := unpeelVecVec ticks v;
    indexAt t sz isz := @indexAtBoolVec t sz isz ticks;
    indexConst t sz := @indexConstBoolVec t sz ticks;
    slice t sz := @sliceBoolVec t sz ticks;
    unsignedAdd m n := @unsignedAddBoolVec m n ticks;
    unsignedMult m n := @unsignedMultBoolVec m n ticks;
    greaterThanOrEqual m n := @greaterThanOrEqualBoolVec m n ticks;
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefaultSV ticks (map port_type (circuitOutputs intf)));
  }.

 Instance SequentialVectorSemantics {ticks: nat}
   : CavaSeq SequentialVectorCombSemantics:=
   { delay k i := delayV ticks k i;
     loop A B C := @loopSeqV A B C ticks;
   }.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition sequentialV {ticks a} (circuit : cava (signal:=seqVType ticks) a) : a := unIdent circuit.
