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
  Aes.sbox
  Aes.mix_single_column
  Aes.sub_bytes
  Aes.shift_rows
  Aes.mix_columns
  Aes.sbox_canright_masked_noreuse
  Aes.sbox_lut
  Aes.sbox_canright
  Aes.pkg
  Aes.cipher_round
  Aes.unrolled_opentitan_cipher
  Aes.unrolled_naive_cipher
  Aes.sbox_canright_pkg
  Aes.aes_test
  Aes.netlists.

Extraction Library sbox.
Extraction Library mix_single_column.
Extraction Library sub_bytes.
Extraction Library shift_rows.
Extraction Library mix_columns.
Extraction Library sbox_canright_masked_noreuse.
Extraction Library sbox_lut.
Extraction Library sbox_canright.
Extraction Library pkg.
Extraction Library sbox_canright_pkg.
Extraction Library cipher_round.
Extraction Library unrolled_naive_cipher.
Extraction Library unrolled_opentitan_cipher.
Extraction Library aes_test.
Extraction Library netlists.
