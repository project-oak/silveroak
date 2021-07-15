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

(* n is the number of delays on the output, m is the number of delays on the
   loop state *)
Definition retimed {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  exists rvals,
    cequiv c1
           (LoopInit (loops_reset_state c2)
                     ((loopless c2)
                        >==> chreset (ndelays (o * loops_state c2) n) rvals)).

Fixpoint retime_loops {i o} (c : Circuit i o) : Circuit i o :=
  match c with
  | Comb f => Comb f
  | Compose f g => Compose (retime_loops f) (retime_loops g)
  | First f => First (retime_loops f)
  | Second f => Second (retime_loops f)
  | LoopInitCE r f => LoopInitCE r (f >==> Second Delay)
  | DelayInit r => DelayInit r
  end.
