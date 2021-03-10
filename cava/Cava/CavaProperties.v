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

(**** Import this file for everything you need to prove properties about Cava
      circuits. ****)

Require Export Cava.Cava.
Require Export Cava.Lib.LibProperties.
Require Export Cava.Semantics.Combinational.
Require Export Cava.Semantics.CombinationalProperties.

(* Proofs about the standard library datatypes that can come in useful *)
Require Export Cava.Util.List.
Require Export Cava.Util.Nat.
Require Export Cava.Util.Vector.

(* Proofs about bit vectors *)
Require Export Cava.Util.BitArithmeticProperties.

(* Generally useful tactics *)
Require Export Coq.micromega.Lia.
Require Export coqutil.Tactics.Tactics.
Require Export Cava.Util.Tactics.

(* Make sure the semantics Cava instance has priority over the
netlist-generating one for proofs *)
Existing Instance CombinationalSemantics.
