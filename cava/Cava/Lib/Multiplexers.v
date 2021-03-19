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
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Require Import Cava.Core.CavaClass.
Require Import Cava.Core.Signal.

(**** IMPORTANT: if you make changes to the API of these definitions, or add new
      ones, make sure you update the reference at docs/reference.md! ****)

Section WithCava.
  Context `{semantics:Cava}.

  (* A two to one multiplexer that takes its two arguments as a pair rather
     than as a 2 element vector which is what indexAt works over. *)
  Definition mux2 {A : SignalType}
             (sel : signal Bit)
             (ab : signal A * signal A) : cava (signal A) :=
    let '(a,b) := ab in
    v <- packV [a;b] ;;
    i <- packV [sel] ;;
    indexAt v i.

  (* 4-element multiplexer *)
  Definition mux4 {t} (input : signal t * signal t * signal t * signal t)
             (sel : signal (Vec Bit 2)) : cava (signal t) :=
    let '(i0,i1,i2,i3) := input in
    v <- packV [i0;i1;i2;i3]%vector ;;
    indexAt v sel.
End WithCava.
