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
Local Open Scope monad_scope.

Require Import Cava.Core.Core.
Require Import Cava.Lib.Combinators.

(**** IMPORTANT: if you make changes to the API of these definitions, or add new
      ones, make sure you update the reference at docs/reference.md! ****)

Section WithCava.
  Context `{semantics:Cava}.

  (* Constant signals. *)

  (* This component always returns the value 0. *)
  Definition zero : signal Bit := constant false.

  (* This component always returns the value 1. *)
  Definition one : signal Bit := constant true.

  Definition all {n} (v : signal (Vec Bit n)) : cava (signal Bit) :=
    match n with
    | 0 => ret one
    | _ => tree and2 v
    end.

  Definition any {n} (v : signal (Vec Bit n)) : cava (signal Bit) :=
    match n with
    | 0 => ret zero
    | _ => tree or2 v
    end.

  Fixpoint eqb {t : SignalType} : signal t * signal t -> cava (signal Bit) :=
    match t as t0 return signal t0 * signal t0 -> cava (signal Bit) with
    | Void => fun _ => ret one
    | Bit => xnor2
    | ExternalType s => fun _ => ret one
    | Vec a n => fun '(x,y) =>
                  eq_results <- Vec.map2 eqb (x, y) ;;
                  all eq_results
    end.
End WithCava.
