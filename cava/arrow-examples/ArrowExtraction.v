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

Require Import Combinators.
Require Import SyntaxExamples.
Require Import Mux2_1.
Require Import UnsignedAdder.

Require Import ArrowAdderTutorial.

Extraction Library Combinators.
Extraction Library SyntaxExamples.
Extraction Library Mux2_1.
Extraction Library UnsignedAdder.

Extraction Library ArrowAdderTutorial.

From Cava Require Import Arrow.ArrowExport.
(* From Cava Require Import Cava.pkg. *)
Extraction Library CavaNotation.
Require Import Aes.pkg.
Extraction Library pkg.
Require Import Aes.sbox.
Extraction Library sbox.
Require Import Aes.sbox_canright_pkg.
Extraction Library sbox_canright_pkg.
Require Import Aes.sbox_canright.
Extraction Library sbox_canright.