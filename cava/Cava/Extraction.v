(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
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

Extraction Language Haskell.

Require Import BitVector.
Require Import Cava.
Require Import Cava.Examples.

Recursive Extraction Library BitVector.
Recursive Extraction Library Combinators.
Recursive Extraction Library Cava.
Extraction Library Examples.

Require Import Cava.Arrow.ArrowExamples.

Recursive Extraction Library ArrowExamples.
