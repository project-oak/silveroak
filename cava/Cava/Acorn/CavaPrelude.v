(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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
Local Open Scope vector_scope.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Acorn.CavaClass.
Require Import Cava.Signal.

Section WithCava.
  Context {signal} `{Cava signal}.

  (* Constant signals. *)

  (* This component always returns the value 0. *)
  Definition zero : signal Bit := constant false.

  (* This component always returns the value 1. *)
  Definition one : signal Bit := constant true.

  (* Ideally muxPair would be in Cava.Lib but we need to use it in the Cava
     core modules for a definition is Sequential.v
  *)

  (* A two to one multiplexer that takes its two arguments as a pair rather
     than as a 2 element vector which is what indexAt works over. *)

  Definition muxPair {A : SignalType}
                     (sel : signal Bit)
                     (ab : signal A * signal A) : cava (signal A) :=
  let (a, b) := ab in
  ret (indexAt (unpeel [a; b]) (unpeel [sel])).

  (* A variant of muxPair that works over a Cava pair. *)
  Definition pairSel {A : SignalType}
                     (sel : signal Bit)
                     (ab : signal (Pair A A)) : signal A :=
  let (a, b) := unpair ab in
  indexAt (unpeel [a; b]) (unpeel [sel]).

  (* A unit delay with a default reset value. *)
  Definition delay {A : SignalType} (i : signal A) : cava (signal A) :=
    delayWith (defaultCombValue A) i.

  (* A unit delay with a clock-enable input and default reset value. *)
  Definition delayEnable {A : SignalType} (en: signal Bit) (i : signal A) : cava (signal A) :=
    delayEnableWith (defaultCombValue A) en i.

End WithCava.
