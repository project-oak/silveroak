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

Require Import coqutil.Z.HexNotation.

Set Extraction Optimize.

Extraction Language Haskell.

Require Import Cava.Arrow.ArrowExport.
Extraction Library CavaNotation.
Extraction Library HexNotation.

Require Import
  Aes.Sbox
  Aes.MixSingleColumn
  Aes.SubBytes
  Aes.ShiftRows
  Aes.MixColumns
  Aes.SboxCanrightMaskedNoReuse
  Aes.SboxLut
  Aes.SboxCanright
  Aes.Pkg
  Aes.CipherRound
  Aes.UnrolledOpenTitanCipher
  Aes.UnrolledNaiveCipher
  Aes.SboxCanrightPkg
  Aes.AesTest
  Aes.Netlist.

Extraction Library Sbox.
Extraction Library MixSingleColumn.
Extraction Library SubBytes.
Extraction Library ShiftRows.
Extraction Library MixColumns.
Extraction Library SboxCanrightMaskedNoReuse.
Extraction Library SboxLut.
Extraction Library SboxCanright.
Extraction Library Pkg.
Extraction Library SboxCanrightPkg.
Extraction Library CipherRound.
Extraction Library UnrolledNaiveCipher.
Extraction Library UnrolledOpenTitanCipher.
Extraction Library AesTest.
Extraction Library Netlist.
