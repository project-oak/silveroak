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

Require Import Cava.Acorn.Combinators.
Require Import Cava.Acorn.CavaPrelude.

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
           (resetValue : combType B)
           (f : seqType A * seqType B -> ident (seqType B))
           (state: nat * ident (seqType B)) (a : combType A)
  : nat * ident (seqType B) :=
  let t := fst state in
  (S t,
   out <- snd state ;; (* get the output accumulator *)
   (* get the value of out at previous timestep (because of delay) *)
   let outDelayed := match t with
                     | 0 => resetValue
                     | S t' => nth t' out (defaultCombValue B)
                     end in
   b <- f ([a], [outDelayed]) ;; (* Process one input *)
   let out' := overlap t out b in (* append new output, starting at timestep t *)
   ret out').

Definition loopSeqS {A B : SignalType}
                    (resetValue : combType B)
                    (f : seqType A * seqType B -> ident (seqType B))
                    (a : seqType A) : ident (seqType B) :=
  snd (fold_left (loopSeqS' resetValue f) a (0, ret [])).


Fixpoint delayEnableBoolList' (t: SignalType) (en: list bool) (i : seqType t)
                              (state: combType t) :
                              ident (seqType t) :=
  match en ,i with
  | enV::enX, iV::iX =>  r <- delayEnableBoolList' t enX iX (if enV then iV else state) ;;
                         ret (state:: r)
  | _, _ => ret []
  end.

Definition delayEnableBoolList (t: SignalType) (def : combType t)
                               (en: list bool) (i : seqType t) :
                               ident (seqType t) :=
  delayEnableBoolList' t en i def.

Definition encodeLoopEnable
  {A B : SignalType}
  (en: seqType Bit)
  (f : seqType A * seqType B -> ident (seqType B))
  (i_state : seqType A * seqType B) :
  ident (seqType B) :=
    let state := snd i_state in
    let i := fst i_state in 
    let newState := unIdent (f (i, state)) in
    if en then ret newState else ret state.

(******************************************************************************)
(* Instantiate the Cava class for a boolean combinational logic               *)
(* interpretation.                                                            *)
(******************************************************************************)

Instance CircuitSemantics : Cava seqType :=
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
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefaultS (map port_type (circuitOutputs intf)));
    delayWith t d i := ret (d :: i);
    delayEnableWith t d en i := delayEnableBoolList t d en i;
    loopDelaySR _ _ := loopSeqS;
    (* The semantics of loopDelaySEnable is defined in terms of loopDelayS and
       the circuitry required to model a clock enable with a multiplexor. *)
    loopDelaySEnableR _ _ resetValue en f input :=
       loopSeqS resetValue (encodeLoopEnable en f) input;
   }.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition semantics {a} (circuit : cava a) : a := unIdent circuit.
