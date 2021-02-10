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

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import AcornAes.SubBytesCircuit.
Require Import AcornAes.Pkg.
Import Pkg.Notations.

(* Interface designed to match interface of corresponding SystemVerilog component:
     https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_sbox_lut.sv
*)
Definition aes_sbox_lut_Interface :=
  combinationalInterface "aes_sbox_lut"
  [mkPort "op_i" Bit; mkPort "data_i" (Vec Bit 8)]
  [mkPort "data_o" (Vec Bit 8)]
  [].

(* Interface designed to match interface of corresponding SystemVerilog component:
     https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_sub_bytes.sv
*)
Definition aes_sub_bytes_Interface :=
  combinationalInterface "aes_sub_bytes"
  [mkPort "op_i" Bit; mkPort "data_i" state]
  [mkPort "data_o" state]
  [].

Definition aes_sbox_lut_Netlist
  := makeNetlist aes_sbox_lut_Interface (fun '(op_i, data_i) => aes_sbox_lut op_i data_i).

Definition aes_sub_bytes_Netlist
  := makeNetlist aes_sub_bytes_Interface (fun '(op_i, data_i) => sub_bytes op_i data_i).

Definition subBytesTestVec : Vector.t (Vector.t nat 4) 4
  := [[219; 19; 83; 69];
      [242; 10; 34; 92];
      [1; 1; 1; 1];
      [45; 38; 49; 76]
  ]%vector.

(* Compute the expected outputs from the Coq/Cava semantics. *)
Definition sub_bytes_expected_outputs := combinational (sub_bytes [false] [fromNatVec subBytesTestVec]).

Definition aes_sub_bytes_tb :=
  testBench "aes_sub_bytes_tb"
            aes_sub_bytes_Interface
            [(false, fromNatVec subBytesTestVec)]
            sub_bytes_expected_outputs.
