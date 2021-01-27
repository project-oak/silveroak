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
Require Import Cava.Acorn.CavaPrelude.

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

(******************************************************************************)
(* Instantiate the Cava class for a boolean sequential logic                  *)
(* interpretation.                                                            *)
(******************************************************************************)

Instance SequentialSemantics : CavaSeq CombinationalSemantics :=
   { delayWith t d i := ret (d :: i);
     delayEnableWith t d en i := delayEnableBoolList t d en i;
     loopDelaySR _ _ := loopSeqS;
     loopDelaySEnableR A B resetValue en f input :=
       (* The semantics of loopDelaySEnable is defined in terms of loopDelayS and
          the circuitry required to model a clock enable with a multiplexor. *)
         loopSeqS resetValue
                  (fun (en_i_state : seqType (Pair Bit A) * seqType B)  =>
                     let state := snd en_i_state in
                     let '(en, i) := unpair (fst en_i_state) in
                     (second fork2 >=> (* (i, state, state) *)
                       pairLeft >=>    (* ((i, state), state) *)
                       first f >=>     (* (f (i, state), state) *)
                       swap >=>        (* (state, f (i, state) *)
                       muxPair en)     (* if en then f (i, state) else state *)
                       (i, state)) (mkpair en input)
   }.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition sequential {A} (circuit : cava A) : A := unIdent circuit.
