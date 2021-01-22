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
  Context {signal} `{Cava signal} `{Monad cava}.

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

End WithCava.
