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

From Coq Require Import Arith.Arith Logic.Eqdep_dec Vectors.Vector micromega.Lia
     NArith.NArith Strings.String NArith.Ndigits.
From Cava Require Import Arrow.ArrowExport BitArithmetic.

From Aes Require Import pkg sbox unrolled_opentitan_cipher.

Require Import Cava.Types.
Require Import Cava.Netlist.

(* Definition sbox_canright_interface *)
(*   := combinationalInterface "sbox_canright" *)
(*      (mkPort "op_i" Kind.Bit, mkPort "data_i" (Kind.Vec Kind.Bit 8)) *)
(*      (mkPort "data_o" (Kind.Vec Kind.Bit 8)) *)
(*      nil. *)

(* Definition sbox_canright_netlist := *)
(*   makeNetlist sbox_canright_interface (build_netlist (closure_conversion (aes_sbox SboxCanright))). *)

(* Definition sbox_lut_interface *)
(*   := combinationalInterface "sbox_lut" *)
(*      (mkPort "op_i" Kind.Bit, mkPort "data_i" (Kind.Vec Kind.Bit 8)) *)
(*      (mkPort "data_o" (Kind.Vec Kind.Bit 8)) *)
(*      nil. *)

(* Definition sbox_lut_netlist := *)
(*   makeNetlist sbox_lut_interface (build_netlist (closure_conversion (aes_sbox SboxLut))). *)

