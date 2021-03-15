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
Require Import AcornAes.ShiftRowsCircuit.
Require Import AcornAes.Pkg.

(* Interface designed to match interface of corresponding SystemVerilog component:
     https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_shift_rows.sv
*)
Definition aes_shift_rows_Interface :=
  combinationalInterface "aes_shift_rows"
  [mkPort "op_i" Bit; mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)]
  [].

Definition aes_shift_rows_Netlist
  := makeNetlist aes_shift_rows_Interface (fun '(op_i, data_i) => aes_shift_rows op_i data_i).

(* Compute the expected outputs from the Coq/Cava semantics. *)
Definition aes_shift_rows_expected_outputs :=
  multistep (Comb (fun '(op_i, data_i) => aes_shift_rows op_i data_i))
            [(false, fromNatVec test_state)].

Definition aes_shift_rows_tb :=
  testBench "aes_shift_rows_tb"
            aes_shift_rows_Interface
            [(false, fromNatVec test_state)]
            aes_shift_rows_expected_outputs.
