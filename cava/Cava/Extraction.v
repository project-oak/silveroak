(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
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

Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrHaskellZInteger.
Require Import Coq.extraction.ExtrHaskellString.
Require Import Coq.extraction.ExtrHaskellBasic.
Require Import Coq.extraction.ExtrHaskellNatInteger.

Extraction Language Haskell.
Set Extraction KeepSingleton.
Set Extraction File Comment "Auto-generated from Cava/Coq. Please do not hand edit.".

Require Import Cava.Cava.
Require Import Cava.Lib.Decoder.
Require Import Cava.Util.Vector.
Require Import Cava.Semantics.Combinational.

Recursive Extraction Library BitArithmetic.
Recursive Extraction Library Cava.
Recursive Extraction Library Circuit.
Recursive Extraction Library Combinational.
Recursive Extraction Library Combinators.
Recursive Extraction Library Identity.
Recursive Extraction Library Simulation.
Recursive Extraction Library NetlistGeneration.

Recursive Extraction Library Netlist.
Recursive Extraction Library Signal.
Recursive Extraction Library Vector.
Recursive Extraction Library Decoder.
Recursive Extraction Library Adders.
Recursive Extraction Library CavaPrelude.

Recursive Extraction Library Multiplexers.
Recursive Extraction Library Vec.
