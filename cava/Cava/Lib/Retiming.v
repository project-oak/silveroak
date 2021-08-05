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
  Fixpoint ndelays (t : type) (n : nat) : Circuit t t :=
    match n with
    | 0 => Id
    | S m => ndelays t m >==> Delay
    end.
End WithCava.

(* mealy machine conversion using [step] *)
Definition mealy {i o} (c : Circuit i o)
  : Circuit (i * circuit_state c) (o * circuit_state c) :=
  Comb
    (i:=i * circuit_state c)
    (o:=o * circuit_state c)
    (fun (xs : value (i * circuit_state c)) =>
       swap (step c (snd xs) (fst xs))).

(* repeat a particular value for each delay in ndelays *)
Fixpoint to_ndelays_state {t n} (x : value t)
  : value (circuit_state (ndelays t n)) :=
    match n with
    | 0 => tt
    | S m => (to_ndelays_state x, x)
    end.

Definition retimed {i o} (n : nat) rvals (c1 c2 : Circuit i o) : Prop :=
  cequiv c1 (LoopInit (reset_state c2)
                      ((mealy c2)
                         >==>
                         (Par (chreset (ndelays o n) rvals)
                              (chreset (ndelays (circuit_state c2) n)
                                       (to_ndelays_state (reset_state c2)))))).
