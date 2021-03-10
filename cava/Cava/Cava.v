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

(* Some pieces of the standard library that are helpful for defining circuits
   and creating test cases *)
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Bool.Bvector.
Require Export Coq.NArith.NArith.
Require Coq.Lists.List.
Require Coq.Vectors.Vector.
Export List.ListNotations Vector.VectorNotations.

(* String definition + notation (for netlist port/interface names) *)
Require Export Coq.Strings.String.
Global Open Scope string_scope.

(* Monad definition + notation *)
Require Export ExtLib.Structures.Monad.
Export MonadNotation.
Global Open Scope monad_scope.

(* Basic infrastructure for defining circuits *)
Require Export Cava.Core.Core.

(* Cava instance + definitions for creating netlists from circuits *)
Require Export Cava.NetlistGeneration.NetlistGeneration.

(* Library of common small circuit components (multiplexers, adders, etc) *)
Require Export Cava.Lib.Lib.

(* Circuit simulation function *)
Require Export Cava.Semantics.Simulation.

(* Bit-arithmetic functions (useful for making small tests) *)
Require Export Cava.Util.BitArithmetic.

(* Monadic fold definitions *)
Require Export Cava.Util.MonadFold.

(* Extra definitions for standard library vectors *)
Require Export Cava.Util.Vector.

(* Make sure the netlist Cava instance has priority over the Coq semantics to
   avoid confusing error messages *)
Existing Instance CavaCombinationalNet.
