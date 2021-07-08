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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Semantics.Loopless.
Require Import Cava.Semantics.WeakEquivalence.
Require Import Cava.Lib.CircuitTransforms.
Require Import Cava.Lib.Combinators.
Require Import Cava.Lib.Multiplexers.
Import ListNotations Circuit.Notations.

Section WithCava.
  Context `{semantics : Cava}.

  (* make a circuit with one delay for each signal, given reset values *)
  Fixpoint delays {t : type} : Circuit t t :=
    match t with
    | tzero => Delay
    | tone t => Delay
    | tpair t1 t2 => Par delays delays
    end.

  (* make a circuit with repeated delays for each signal *)
  Fixpoint ndelays {t : type} (n : nat) : Circuit t t :=
    match n with
    | 0 => Id
    | S m => ndelays m >==> delays
    end.
End WithCava.

(* n is delays on state; m is delays on input *)
Definition phase_retimed {i o} (n m : nat) (c1 c2 : Circuit i o) : Prop :=
  exists (proj21 : value (loops_state c2) -> value (loops_state c1))
    (proj12 : value (loops_state c1) -> value (loops_state c2)),
    (forall x, proj12 (proj21 x) = x)
    /\ wequiv (loopless c1)
             (Second (Comb proj12)
                   >==> Par (ndelays m) (ndelays n)
                   >==> loopless c2
                   >==> Second (Comb proj21)).
