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

Require Import AesImpl.Pkg.
Require Import AesImpl.CipherCircuit.
Require Import AesImpl.CipherCircuit.
Require Import AesImpl.MixColumnsCircuit.
Require Import AesImpl.ShiftRowsCircuit.
Require Import AesImpl.SubBytesCircuit.
Require Import AesImpl.AddRoundKeyCircuit.
Require Import AesImpl.CipherControlCircuit.
Require Import AesImpl.MixColumnsNetlist.
Require Import AesImpl.ShiftRowsNetlist.
Require Import AesImpl.SubBytesNetlist.
Require Import AesImpl.AddRoundKeyNetlist.
Require Import AesImpl.CipherControlNetlist.
Require Import AesImpl.FFunctor.
Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrHaskellZInteger.
Require Import Coq.extraction.ExtrHaskellString.
Require Import Coq.extraction.ExtrHaskellBasic.
Require Import Coq.extraction.ExtrHaskellNatInteger.
Require Import RecordUpdate.RecordSet.

Extraction Language Haskell.

Extraction Library Pkg.
Extraction Library CipherCircuit.
Extraction Library MixColumnsCircuit.
Extraction Library ShiftRowsCircuit.
Extraction Library SubBytesCircuit.
Extraction Library AddRoundKeyCircuit.
Extraction Library CipherControlCircuit.
Extraction Library MixColumnsNetlist.
Extraction Library ShiftRowsNetlist.
Extraction Library SubBytesNetlist.
Extraction Library AddRoundKeyNetlist.
Extraction Library CipherControlNetlist.
Extraction Library RecordSet.
Extraction Library FFunctor.
