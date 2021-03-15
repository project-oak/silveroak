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
Require Import AcornAes.MixColumnsCircuit.
Require Import AcornAes.Pkg.

(* Interface designed to match interface of corresponding SystemVerilog component:
     https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_mix_columns.sv
*)
Definition aes_mix_columns_Interface :=
  combinationalInterface "aes_mix_columns"
  [mkPort "op_i" Bit; mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)]
  [].

(* Create a netlist for the aes_mix_columns_Netlist block. The block is written with
   curried inputs but netlist extraction for top-level blocks requires they are
   written with a single argument, using tupling for composite inputs. A lambda
   expression maps from the tuple inputs to the curried arguments.  *)
Definition aes_mix_columns_Netlist
  := makeNetlist aes_mix_columns_Interface (fun '(op_i, data_i) => aes_mix_columns op_i data_i).

Local Open Scope list_scope.

(* Compute the expected outputs from the Coq/Cava semantics. *)
Definition aes_mix_cols_expected_outputs :=
  multistep (Comb (fun '(op_i, data_i) => aes_mix_columns op_i data_i))
            [(false, fromNatVec test_state)].

Definition aes_mix_columns_tb :=
  testBench "aes_mix_columns_tb"
            aes_mix_columns_Interface
            [(false, fromNatVec test_state)]
            aes_mix_cols_expected_outputs.
