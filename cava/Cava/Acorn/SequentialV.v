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
Require Import Cava.Acorn.CavaPrelude.
Require Import Cava.Acorn.CombinationalMonad.

Local Open Scope vector_scope.


Local Open Scope type_scope.

(* stepOnce is a helper function that takes a circuit running for > 1 ticks and
   runs it for only one tick. *)
Definition stepOnce {m} `{Monad m}  {A B : SignalType} {ticks : nat}
           (f : seqVType (S ticks) A * seqVType (S ticks) B -> m (seqVType (S ticks) B))
           (input : seqVType 1 A * seqVType 1 B) : m (seqVType 1 B) :=
  let a := Vector.hd (fst input) in
  let b := Vector.hd (snd input) in
  b <- f (a :: const (defaultCombValue A) ticks, b :: const (defaultCombValue B) ticks) ;;
  ret ([Vector.hd b]).

(******************************************************************************)
(* Loop combinator for feedback with delay.                                   *)
(******************************************************************************)

(*
loopSeqSV' takes a combinational circuit f which has a pair of inputs which
represent the current input of type A and current state of type C. This circuit
returns a pair which represents the computed output of type B and next state
value of type C. The list of input values for each clock tick are provided
by the a parameter and the current state value is provided by the feedback
parameter. The result of the loopSeq' is a list in the identity monad that
represented the list of computed values at each tick.
*)

Fixpoint loopSeqSV' {m} `{Monad m}
                   {A B : SignalType}
                   (ticks: nat)
                   (f : seqVType 1 A * seqVType 1 B -> m (seqVType 1 B))
                   {struct ticks}
  : seqVType ticks A -> seqVType 1 B -> m (seqVType ticks B) :=
  match ticks as ticks0 return seqVType ticks0 A -> _ -> m (seqVType ticks0 B) with
  | O => fun _ _ => ret []
  | S ticks' =>
    fun a feedback =>
      let x := Vector.hd a in
      let xs := Vector.tl a in
      nextState <- f ([x], feedback) ;; (* One step of f. *)
      ys <- loopSeqSV' ticks' f xs nextState ;; (* remaining steps of f *)
      ret (nextState ++ ys)
  end.

(*
The loopSeqSV combinator takes a combinational circuit f which maps a pair
representing the current input and current state to another pair
representing the computed output and next state value. This function is used
to compute the sequential behaviour of a circuit which uses f to iterate over
the a inputs, using a default value for the initial state.
 *)

Definition loopSeqSV {A B : SignalType} (ticks : nat) (resetval : combType B)
  : (seqVType ticks A * seqVType ticks B -> ident (seqVType ticks B))
    -> seqVType ticks A -> ident (seqVType ticks B) :=
  match ticks as ticks0 return
        (seqVType ticks0 A * seqVType ticks0 B -> ident (seqVType ticks0 B))
        -> seqVType ticks0 A -> ident (seqVType ticks0 B)  with
  | O => fun _ _ => ret []
  | S ticks' =>
    fun f a =>
      loopSeqSV' (S ticks') (stepOnce f) a [resetval]
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

Definition indexConstBoolVec {t: SignalType}
                          {sz : nat}
                          (ticks: nat)
                          (i : Vector.t (Vector.t (combType t) sz) ticks)
                          (sel : nat)
                          : Vector.t (combType t) ticks :=
  Vector.map (fun i => nth_default (defaultCombValue t) sel i) i.

Definition indexAtBoolVec {t: SignalType}
                          {sz isz: nat}
                          (ticks: nat)
                          (i : Vector.t (Vector.t (combType t) sz) ticks)
                          (sel : Vector.t (Bvector isz) ticks)
                          : Vector.t (combType t) ticks :=
  Vector.map (fun '(i, sel) => nth_default (defaultCombValue t) (N.to_nat (Bv2N sel)) i)
             (vcombine i sel).

Definition sliceBoolVec {t: SignalType}
                        {sz: nat}
                        (ticks: nat)
                        (startAt len : nat)
                        (v: Vector.t (Vector.t (combType t) sz) ticks)
                        (H: startAt + len <= sz) :
                        Vector.t (Vector.t (combType t) len) ticks :=
  Vector.map (fun v => sliceVector v startAt len H) v.

Definition peelVecVec {t: SignalType} {s: nat}
                      (ticks: nat)
                      (v: Vector.t (Vector.t (combType t) s) ticks)
                      : Vector.t (Vector.t (combType t) ticks) s :=
  Vector.map (indexConstBoolVec _ v) (vseq 0 s).

Definition unpeelVecVec {t: SignalType} {s: nat}
                        (ticks: nat)
                        (v: Vector.t (Vector.t (combType t) ticks) s)
                        : Vector.t (Vector.t (combType t) s) ticks :=
  Vector.map
    (fun ni => Vector.map (fun vi => nth_default (defaultCombValue t) ni vi) v)
    (vseq 0 ticks).

Definition bufBoolVec (ticks: nat)
           (i : Vector.t bool ticks) : ident (Vector.t bool ticks) :=
  ret i.

Definition delayV (ticks : nat) (t : SignalType) (def : combType t) : seqVType ticks t -> ident (seqVType ticks t) :=
  match ticks as ticks0 return seqVType ticks0 t -> ident (seqVType ticks0 t) with
  | O => fun _ => ret []
  | S ticks' => fun i => ret (def  :: Vector.shiftout i)
  end.

(******************************************************************************)
(* Instantiate the Cava class for a boolean sequential logic                  *)
(* interpretation.                                                            *)
(******************************************************************************)

(*

TODO: Work out if there is a sensible way to reintroduce SequentialVectorCombSemantics

 Instance SequentialVectorCombSemantics {ticks: nat} : Cava (seqVType ticks) :=
  { cava := ident;
    constant b := Vector.const b ticks;
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
    mkpair _ _ v1 v2:= vcombine v1 v2;
    unpair _ _ v := separate v;
    peel _ _ v := peelVecVec ticks v;
    unpeel _ _ v := unpeelVecVec ticks v;
    indexAt t sz isz := @indexAtBoolVec t sz isz ticks;
    indexConst t sz := @indexConstBoolVec t sz ticks;
    slice t sz := @sliceBoolVec t sz ticks;
    unsignedAdd m n xy := Vector.map (@unsignedAddBool m n) (vcombine (fst xy) (snd xy));
    unsignedMult m n xy := Vector.map (@unsignedMultBool m n) (vcombine (fst xy) (snd xy));
    greaterThanOrEqual m n xy := Vector.map (@greaterThanOrEqualBool m n) (vcombine (fst xy) (snd xy));
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefaultSV ticks (map port_type (circuitOutputs intf)));
  }.

 Instance SequentialVectorSemantics {ticks: nat}
   : CavaSeq SequentialVectorCombSemantics:=
   { delayWith k d i := delayV ticks k d i;
     (* Dummy definition now for delayEnable.
        TODO(satnam6502, jadephilipoom): implement delayEnableV
     *)
     delayEnableWith k d en i := delayV ticks k d i;
     loopDelaySR A B := @loopSeqSV A B ticks;
     (* TODO(satnam6502, jadep): Placeholder definition for loopDelayEnable for
        now. Replace with actual definition that models clock enable behaviour.
     *)
     loopDelaySEnableR A B resetval en := @loopSeqSV A B ticks resetval; (* Dummy *)
   }.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition sequentialV {ticks a} (circuit : cava (signal:=seqVType ticks) a) : a := unIdent circuit.

*)