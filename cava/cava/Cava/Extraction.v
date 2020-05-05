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

From Coq Require Import Extraction.
From Coq Require Import extraction.ExtrHaskellZInteger.
From Coq Require Import extraction.ExtrHaskellString.
From Coq Require Import ExtrHaskellBasic.
From Coq Require Import extraction.ExtrHaskellNatInteger.

Extraction Language Haskell.

Require Import Cava.BitArithmetic.
Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Monad.UnsignedAdders.
Require Import Cava.Monad.XilinxAdder.

Recursive Extraction Library BitArithmetic.
Recursive Extraction Library Cava.
Recursive Extraction Library Combinators.

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Syntax.
Require Import Cava.Arrow.Instances.Coq.
Require Import Cava.Arrow.Instances.Netlist.
Recursive Extraction Library Arrow.
Recursive Extraction Library Syntax.

Recursive Extraction Library Coq.
Recursive Extraction Library Netlist.
Recursive Extraction Library UnsignedAdders.
Recursive Extraction Library XilinxAdder.
