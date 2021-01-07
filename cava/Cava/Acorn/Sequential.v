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
Require Import Cava.Tactics.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.CombinationalMonad.
Require Import Cava.Acorn.Combinators.

(* Given two sequential inputs, combine them by combining all the elements of
   the first with the elements of the second that *do not overlap* when the
   second is offset from the first by the specified offset. For example:

   a1 = [0;0;1], a2 = [0;0;2], offset = 1:
   a1            : 0 0 1
   a2            :   0 0 2
   overlap a1 a2 : 0 0 1 2

   a1 = [0;1;2;3], a2 = [4;5;6], offset = 2:
   a1            : 0 1 2 3
   a2            :     4 5 6
   overlap a1 a2 : 0 1 2 3 6

   a1 = [0;1;2;3], a2 = [4;5;6], offset = 6:
   a1            : 0 1 2 3
   a2            :             4 5 6
   overlap a1 a2 : 0 1 2 3 0 0 4 5 6

   This is particularly useful for chaining repeated outputs of a circuit with
   delays. *)
Definition overlap {A} (offset : nat) (a1 a2 : seqType A) : seqType A :=
  a1 ++ repeat (defaultCombValue A) (offset - length a1) ++ skipn (length a1 - offset) a2.

(******************************************************************************)
(* Loop combinator for feedback with delay.                                   *)
(******************************************************************************)

(* loopSeqS' performs a single loop step, given a state consisting of the
timestep and the accumulator for (past) output values. This loop step
represents a circuit in which the output and the feedback are the same:
        _______
    ---| delay |-------
   |   |_______|       |
   |   ______          |
    --| body |----------------- out
 in --|______|

The nth value in the output accumulator is always the output value for
timestep n. Because there may be delay in the body of the loop, the accumulator
might include outputs past the current timestep. *)

Definition loopSeqS' {A B : SignalType}
           (f : seqType A * seqType B -> ident (seqType B))
           (state: nat * ident (seqType B)) (a : combType A)
  : nat * ident (seqType B) :=
  let t := fst state in
  (S t,
   out <- snd state ;; (* get the output accumulator *)
   (* get the value of out at previous timestep (because of delay) *)
   let outDelayed := match t with
                     | 0 => defaultCombValue B
                     | S t' => nth t' out (defaultCombValue B)
                     end in
   b <- f ([a], [outDelayed]) ;; (* Process one input *)
   let out' := overlap t out b in (* append new output, starting at timestep t *)
   ret out').

Definition loopSeqS {A B : SignalType}
                    (f : seqType A * seqType B -> ident (seqType B))
                    (a : seqType A) : ident (seqType B) :=
  snd (fold_left (loopSeqS' f) a (0, ret [])).

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

Definition pairSelList {t: SignalType}
                       (sel : list bool) (v: list (combType t * combType t))
  : list (combType t) :=
  ListUtils.map2 pairSelBool sel v.

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

Fixpoint delayEnableBoolList' (t: SignalType) (en: list bool) (i : seqType t)
                              (state: combType t) :
                              ident (seqType t) :=
  match en ,i with
  | enV::enX, iV::iX =>  r <- delayEnableBoolList' t enX iX (if enV then iV else state) ;;
                         ret (state:: r)
  | _, _ => ret []
  end.                         

Definition delayEnableBoolList (t: SignalType) (en: list bool) (i : seqType t) :
                             ident (seqType t) :=
  delayEnableBoolList' t en i (defaultCombValue t).

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
    mkpair _ _ v1 v2 := combine v1 v2;
    unpair _ _ v := split v;
    peel _ _ v := peelVecList v;
    unpeel _ _ v := unpeelVecList v;
    pairSel _ v sel := pairSelList v sel;
    indexAt t sz isz := @indexAtBoolList t sz isz;
    indexConst t sz := @indexConstBoolList t sz;
    slice t sz := @sliceBoolList t sz;
    unsignedAdd m n := @unsignedAddBoolList m n;
    unsignedMult m n := @unsignedMultBoolList m n;
    greaterThanOrEqual m n := @greaterThanOrEqualBoolList m n;
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefaultS (map port_type (circuitOutputs intf)));
  }.

 Instance SequentialSemantics : CavaSeq SequentialCombSemantics :=
   { delay t i := ret (@defaultCombValue t :: i);
     delayEnable t en i := delayEnableBoolList t en i;
     loopDelayS _ _ := loopSeqS;
     loopDelaySEnable A B en f input :=
       (* The semantics of loopDelaySEnable is defined in terms of loopDelayS and
          the circuitry required to model a clock enable with a multiplexor. *)
         loopSeqS (fun (en_i_state : seqType (Pair Bit A) * seqType B)  =>
                     let state := snd en_i_state in
                     let '(en, i) := unpair (fst en_i_state) in
                     (second fork2 >=> (* (i, state, state) *)
                       pairLeft >=>    (* ((i, state), state) *)
                       first f >=>     (* (f (i, state), state) *)
                       swap >=>        (* (state, f (i, state) *)
                       mux2 en)        (* if en then f (i, state) else state *)
                       (i, state)) (mkpair en input)
   }.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition sequential {A} (circuit : cava A) : A := unIdent circuit.
