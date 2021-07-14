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
  (* make a circuit with repeated delays for each signal *)
  Fixpoint ndelays {t : type} (n : nat) : Circuit t t :=
    match n with
    | 0 => Id
    | S m => ndelays m >==> Delay
    end.
End WithCava.

(* n is the number of delays on the output, m is the number of delays on the
   loop state *)
Definition retimed {i o} (n m : nat) (c1 c2 : Circuit i o) : Prop :=
  (* there exists some way of converting between the loop states of c1 and c2 *)
  exists (proj21 : value (loops_state c2) -> value (loops_state c1))
    (proj12 : value (loops_state c1) -> value (loops_state c2)),
    (forall x, proj12 (proj21 x) = x)
    (* ...and loopless c1 is equivalent to loopless c2 composed with the delay
       circuits and the state projections *)
    /\ cequiv (loopless c1)
             (Second (Comb proj12)
                     >==> loopless c2
                     >==> Par (ndelays n) (ndelays m)
                     >==> Second (Comb proj21)).
