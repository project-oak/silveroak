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

Set Extraction Optimize.

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


Require Import
  Aes.sbox
  Aes.mix_single_column
  Aes.sub_bytes
  Aes.shift_rows
  Aes.mix_columns
  Aes.sbox_canright_masked_noreuse
  (* Aes.sbox_lut *)
  Aes.sbox_canright
  Aes.pkg
  Aes.unrolled_cipher
  Aes.sbox_canright_pkg.

Extraction Library sbox.
Extraction Library mix_single_column.
Extraction Library sub_bytes.
Extraction Library shift_rows.
Extraction Library mix_columns.
Extraction Library sbox_canright_masked_noreuse.
(* Extraction Library sbox_lut. *)
Extraction Library sbox_canright.
Extraction Library pkg.
Extraction Library unrolled_cipher.
Extraction Library sbox_canright_pkg.
