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

Require Import Cava.Cava.
Require Import AesSpec.AES256.
Require Import AesSpec.Tests.Common.
Require Import AesSpec.Tests.TestVectors.
Require Import AesImpl.MixColumnsCircuit.
Require Import AesImpl.Pkg.

(* Interface designed to match interface of corresponding SystemVerilog component:
     https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_mix_columns.sv
*)
Definition aes_mix_columns_Interface :=
  combinationalInterface "aes_mix_columns"
  [mkPort "op_i" Bit; mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)].

(* Create a netlist for the aes_mix_columns_Netlist block. The block is written with
   curried inputs but netlist extraction for top-level blocks requires they are
   written with a single argument, using tupling for composite inputs. A lambda
   expression maps from the tuple inputs to the curried arguments.  *)
Definition aes_mix_columns_Netlist
  := makeNetlist aes_mix_columns_Interface (fun '(op_i, data_i) => aes_mix_columns op_i data_i).

(* Test bench checking that for a single step, the circuit and Coq semantics
   return the same result *)
Section SimpleTestBench.
  (* Compute the expected outputs from the Coq/Cava semantics. *)
  Definition aes_mix_cols_simple_inputs : list _ :=
    [(false, fromNatVec test_state)].

  (* Compute the expected outputs from the Coq/Cava semantics. *)
  Definition aes_mix_cols_simple_expected_outputs :=
    simulate (Comb (fun '(op_i, data_i) => aes_mix_columns op_i data_i))
             aes_mix_cols_simple_inputs.
End SimpleTestBench.

(* Test bench checking against full FIPS AES-256 encryption test vector *)
Section FIPSEncryptTestBench.
  Definition aes_mix_columns_enc_tb_inputs :=
    Eval vm_compute in
      (map (fun v => (false, from_flat v))
           (get_state_inputs MixColumns fips_c3_forward)).

  Definition aes_mix_columns_enc_expected_outputs :=
    Eval vm_compute in
      (map from_flat (get_state_outputs MixColumns fips_c3_forward)).
End FIPSEncryptTestBench.

(* Test bench checking against full FIPS AES-256 decryption test vector (for
   equivalent inverse cipher) *)
Section FIPSDecryptTestBench.
  Definition aes_mix_columns_dec_tb_inputs :=
    Eval vm_compute in
      (map (fun v => (true, from_flat v))
           (get_state_inputs InvMixColumns fips_c3_equivalent_inverse)).

  Definition aes_mix_columns_dec_expected_outputs :=
    Eval vm_compute in
      (map from_flat (get_state_outputs InvMixColumns fips_c3_equivalent_inverse)).
End FIPSDecryptTestBench.

(* Concatenate inputs from all tests *)
Definition aes_mix_columns_tb_all_inputs :=
  Eval vm_compute in
    (aes_mix_cols_simple_inputs
       ++ aes_mix_columns_enc_tb_inputs
       ++ aes_mix_columns_dec_tb_inputs)%list.

(* Concatenate expected outputs from all tests *)
Definition aes_mix_columns_tb_all_expected_outputs :=
  Eval vm_compute in
    (aes_mix_cols_simple_expected_outputs
       ++ aes_mix_columns_enc_expected_outputs
       ++ aes_mix_columns_dec_expected_outputs)%list.

Definition aes_mix_columns_tb :=
  testBench "aes_mix_columns_tb"
            aes_mix_columns_Interface
            aes_mix_columns_tb_all_inputs
            aes_mix_columns_tb_all_expected_outputs.
