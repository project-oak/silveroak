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
Require Import ExtLib.Structures.Monads.
Import VectorNotations MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.CavaPrelude.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Combinators.

(******************************************************************************)
(* Inductive to capture circuit's sequential structure                        *)
(******************************************************************************)

Section WithCava.
  Context `{semantics:Cava}.

  (* TODO: change loop here to a loop with enable *)
  (* TODO: maybe make loop have separate in/out types to reduce state info *)
  Inductive Circuit : Type -> Type -> Type :=
  | Comb : forall {i o}, (i -> cava o) -> Circuit i o
  | Compose : forall {i t o}, Circuit i t -> Circuit t o -> Circuit i o
  | First : forall {i o t}, Circuit i o -> Circuit (i * t) (o * t)
  | Second : forall {i o t}, Circuit i o -> Circuit (t * i) (t * o)
  | LoopInitCE :
      forall {i o : Type} {s : SignalType} (en : signal Bit) (resetval : signal s),
        Circuit (i * signal s) (o * signal s) ->
        Circuit i o
  | DelayInitCE :
      forall {t} (en : signal Bit) (resetval : signal t),
        Circuit (signal t) (signal t)
  .

  (* Internal state of the circuit (register values) *)
  Fixpoint circuit_state {i o} (c : Circuit i o) : Type :=
    match c with
    | Comb _ => unit
    | Compose f g => circuit_state f * circuit_state g
    | First f => circuit_state f
    | Second f => circuit_state f
    | @LoopInitCE i o s _ _ f => circuit_state f * signal s
    | @DelayInitCE t _ _ => signal t
    end.

  (* The state of the circuit after a reset *)
  Fixpoint reset_state {i o} (c : Circuit i o) : circuit_state c :=
    match c as c return circuit_state c with
    | Comb _ => tt
    | Compose f g => (reset_state f, reset_state g)
    | First f => reset_state f
    | Second f => reset_state f
    | LoopInitCE _ resetval f => (reset_state f, resetval)
    | DelayInitCE _ resetval => resetval
    end.

  (* Run circuit for a single step *)
  Fixpoint interp {i o} (c : Circuit i o)
    : circuit_state c -> i -> cava (o * circuit_state c) :=
    match c in Circuit i o return circuit_state c -> i
                                  -> cava (o * circuit_state c) with
    | Comb f => fun _ i => x <- f i ;; ret (x, tt)
    | Compose f g =>
      fun cs input =>
        '(x, cs1) <- interp f (fst cs) input ;;
        '(y, cs2) <- interp g (snd cs) x ;;
        ret (y, (cs1, cs2))
    | First f =>
      fun cs input =>
        '(x, cs') <- interp f cs (fst input) ;;
        ret (x, snd input, cs')
    | Second f =>
      fun cs input =>
        '(x, cs') <- interp f cs (snd input) ;;
        ret (fst input, x, cs')
    | LoopInitCE en _ f =>
      fun '(cs,st) input =>
        '(out, st', cs') <- interp f cs (input, st) ;;
        (* select the updated state only if the loop is enabled *)
         let new_state := indexAt (unpeel [st;st']) (unpeel [en]) in
        ret (out, (cs',new_state))
    | DelayInitCE en _ =>
      fun st input =>
        (* select the updated state only if the delay is enabled *)
        let new_state := indexAt (unpeel [st;input]) (unpeel [en]) in
        ret (st, new_state)
    end.

  (* Loop with no enable; set enable to always be true *)
  Definition LoopInit {i o s} (resetval : signal s)
    : Circuit (i * signal s) (o * signal s) -> Circuit i o :=
    LoopInitCE (constant true) resetval.
  (* Delay with no enable; set enable to always be true *)
  Definition DelayInit {t} (resetval : signal t)
    : Circuit (signal t) (signal t) :=
    DelayInitCE (constant true) resetval.

  (* Loop with the default signal as its reset value *)
  Definition LoopCE {i o s} (en : signal Bit)
    : Circuit (i * signal s) (o * signal s) -> Circuit i o :=
    LoopInitCE en defaultSignal.
  (* Delay with the default signal as its reset value *)
  Definition DelayCE {t} (en : signal Bit)
    : Circuit (signal t) (signal t) :=
    DelayInitCE en defaultSignal.

  (* Loop with the default signal as its reset value and no enable *)
  Definition Loop {i o s}
    : Circuit (i * signal s) (o * signal s) -> Circuit i o :=
    LoopInitCE (constant true) defaultSignal.
  (* Delay with the default signal as its reset value and no enable *)
  Definition Delay {t} : Circuit (signal t) (signal t) :=
    DelayInitCE (constant true) defaultSignal.
End WithCava.

Module Notations.
  Infix ">==>" := Compose (at level 40, left associativity).
End Notations.
