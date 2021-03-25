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

Require Import Tests.Instantiate.
Require Import Tests.MuxTests.
Require Import Tests.TestMultiply.
Require Import Tests.Delay.
Require Import Tests.CountBy.CountBy.
Require Import Tests.DoubleCountBy.DoubleCountBy.
Require Import Tests.AccumulatingAdderEnable.AccumulatingAdderEnable.
Require Import Tests.Array.
Require Import Tests.TestVecConstEq.
Require Import Tests.TestDecoder.

Extraction Library Instantiate.
Extraction Library MuxTests.
Extraction Library TestMultiply.
Extraction Library Delay.
Extraction Library AccumulatingAdderEnable.
Extraction Library CountBy.
Extraction Library DoubleCountBy.
Extraction Library Array.
Extraction Library TestVecConstEq.
Extraction Library TestDecoder.
