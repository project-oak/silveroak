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


(**** Import this file for everything you need to define and test circuits with
      Cava. ****)

(* Basic infrastructure for defining circuits *)
Require Export Cava.Core.Core.

(* Cava instance + definitions for creating netlists from circuits *)
Require Export Cava.NetlistGeneration.NetlistGeneration.

(* Library of common small circuit components (multiplexers, adders, etc) *)
Require Export Cava.Lib.Lib.

(* Cava instance for Coq semantics *)
Require Export Cava.Semantics.Combinational.

(* Circuit simulation function *)
Require Export Cava.Semantics.Simulation.

(* Bit-arithmetic functions (useful for making small tests) *)
Require Export Cava.Util.BitArithmetic.
