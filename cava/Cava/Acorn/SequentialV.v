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
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.CombinationalMonad.

Local Open Scope vector_scope.


Local Open Scope type_scope.

(* Peels off the first signals from each member of a collection of signals *)
Fixpoint nil_signals (t : SignalInterface)
  : signals_gen (seqVType 0) t :=
  match t as t return signals_gen (seqVType 0) t with
  | ione t => []
  | ipair t1 t2 => (nil_signals t1, nil_signals t2)
  end.

(* Peels off the first signals from each member of a collection of signals *)
Fixpoint uncons_signals {A : SignalInterface} {ticks: nat}
  : signals_gen (seqVType (S ticks)) A
    -> signals_gen (seqVType 1) A * signals_gen (seqVType ticks) A :=
  match A as A return signals_gen (seqVType (S ticks)) A
    -> signals_gen (seqVType 1) A * signals_gen (seqVType ticks) A with
  | ione t => fun i : seqVType (S _) t => ([Vector.hd i], Vector.tl i)
  | ipair t1 t2 =>
    fun i => let '(hd1, tl1) := uncons_signals (fst i) in
          let '(hd2, tl2) := uncons_signals (snd i) in
          ((hd1, hd2), (tl1, tl2))
  end.

(* The inverse of uncons_signals; reassembles a collection of signals *)
Fixpoint cons_signals {A : SignalInterface} {ticks: nat}
  : signals_gen (seqVType 1) A -> signals_gen (seqVType ticks) A
    -> signals_gen (seqVType (S ticks)) A :=
  match A as A return signals_gen (seqVType 1) A -> signals_gen (seqVType ticks) A
                      -> signals_gen (seqVType (S ticks)) A with
  | ione t => fun i0 i => (i0 ++ i)%vector
  | ipair t1 t2 =>
    fun i0 i => (cons_signals (fst i0) (fst i), cons_signals (snd i0) (snd i))
  end.

Fixpoint default_signals {A : SignalInterface} (ticks: nat)
  : signals_gen (seqVType ticks) A :=
  match A as A return signals_gen (seqVType ticks) A with
  | ione t => Vector.const (defaultCombValue t) ticks
  | ipair t1 t2 => (default_signals ticks, default_signals ticks)
  end.

Fixpoint shiftout_signals {A : SignalInterface} {ticks: nat}
  : signals_gen (seqVType (S ticks)) A -> signals_gen (seqVType ticks) A :=
  match A as A return signals_gen (seqVType (S ticks)) A
                      -> signals_gen (seqVType ticks) A with
  | ione t => fun v => Vector.shiftout v
  | ipair t1 t2 => fun v => (shiftout_signals (fst v), shiftout_signals (snd v))
  end.

(* stepOnce is a helper function that takes a circuit running for > 1 ticks and
   runs it for only one tick. *)
Definition stepOnce {m} `{Monad m}  {A B : SignalInterface} {ticks : nat}
           (f : signals_gen (seqVType (S ticks)) A * signals_gen (seqVType (S ticks)) B
                -> m (signals_gen (seqVType (S ticks)) B))
           (input : signals_gen (seqVType 1) A * signals_gen (seqVType 1) B)
  : m (signals_gen (seqVType 1) B) :=
  b <- f (cons_signals (fst input) (default_signals ticks),
         cons_signals (snd input) (default_signals ticks)) ;;
  ret (fst (uncons_signals b)).

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
                   {A B : SignalInterface}
                   (ticks: nat)
                   (f : signals_gen (seqVType 1) A * signals_gen (seqVType 1) B
                        -> m (signals_gen (seqVType 1) B))
                   {struct ticks}
  : signals_gen (seqVType ticks) A -> signals_gen (seqVType 1) B
    -> m (signals_gen (seqVType ticks) B) :=
  match ticks as ticks0 return signals_gen (seqVType ticks0) A -> _
                               -> m (signals_gen (seqVType ticks0) B) with
  | O => fun _ _ => ret (nil_signals _)
  | S ticks' =>
    fun a feedback =>
      let '(x,xs) := uncons_signals a in
      nextState <- f (x, feedback) ;; (* One step of f. *)
      ys <- loopSeqSV' ticks' f xs nextState ;; (* remaining steps of f *)
      ret (cons_signals nextState ys)
  end.

(*
The loopSeqSV combinator takes a combinational circuit f which maps a pair
representing the current input and current state to another pair
representing the computed output and next state value. This function is used
to compute the sequential behaviour of a circuit which uses f to iterate over
the a inputs, using a default value for the initial state.
 *)

Definition loopSeqSV {A B : SignalInterface} (ticks : nat)
  : (signals_gen (seqVType ticks) A * signals_gen (seqVType ticks) B
     -> ident (signals_gen (seqVType ticks) B))
    -> signals_gen (seqVType ticks) A -> ident (signals_gen (seqVType ticks) B) :=
  match ticks as ticks0 return
        (signals_gen (seqVType ticks0) A * signals_gen (seqVType ticks0) B
         -> ident (signals_gen (seqVType ticks0) B))
        -> signals_gen (seqVType ticks0) A
        -> ident (signals_gen (seqVType ticks0) B)  with
  | O => fun _ _ => ret (nil_signals _)
  | S ticks' =>
    fun f a =>
      loopSeqSV' (S ticks') (stepOnce f)
                a (default_signals _)
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


Definition delayV (ticks : nat) (t : SignalInterface)
  : signals_gen (seqVType ticks) t -> ident (signals_gen (seqVType ticks) t) :=
  match ticks as ticks0 return signals_gen (seqVType ticks0) t
                               -> ident (signals_gen (seqVType ticks0) t) with
  | O => fun _ => ret (nil_signals _)
  | S ticks' => fun i => ret (cons_signals (default_signals _) (shiftout_signals i))
  end.

(******************************************************************************)
(* Instantiate the Cava class for a boolean sequential logic                  *)
(* interpretation.                                                            *)
(******************************************************************************)

 Instance SequentialVectorCombSemantics {ticks: nat} : Cava (seqVType ticks) :=
  { cava := ident;
    constant b := Vector.const b ticks;
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
    unsignedAdd m n x y := ret (Vector.map2 (@unsignedAddBool m n) x y);
    unsignedMult m n x y := ret (Monad:=Monad_ident) (Vector.map2 (@unsignedMultBool m n) x y);
    greaterThanOrEqual m n x y := ret (Vector.map2 (@greaterThanOrEqualBool m n) x y);
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefaultSV ticks (map port_type (circuitOutputs intf)));
  }.

 Instance SequentialVectorSemantics {ticks: nat}
   : CavaSeq SequentialVectorCombSemantics:=
   { delay k i := delayV ticks k i;
     (* Dummy definition now for delayEnable.
        TODO(satnam6502, jadephilipoom): implement delayEnableV
     *)
     delayEnable k en i := delayV ticks k i;
     loopDelayS A B := @loopSeqSV A B ticks;
     (* TODO(satnam6502, jadep): Placeholder definition for loopDelayEnable for
        now. Replace with actual definition that models clock enable behaviour.
     *)
     loopDelaySEnable A B en := @loopSeqSV A B ticks; (* Dummy *)
   }.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition sequentialV {ticks a} (circuit : cava (signal:=seqVType ticks) a) : a := unIdent circuit.
