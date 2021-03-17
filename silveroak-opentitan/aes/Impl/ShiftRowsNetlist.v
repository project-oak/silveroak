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
Require Import AesImpl.ShiftRowsCircuit.
Require Import AesImpl.Pkg.

(* Interface designed to match interface of corresponding SystemVerilog component:
     https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_shift_rows.sv
*)
Definition aes_shift_rows_Interface :=
  combinationalInterface "aes_shift_rows"
  [mkPort "op_i" Bit; mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)].

Definition aes_shift_rows_Netlist
  := makeNetlist aes_shift_rows_Interface (fun '(op_i, data_i) => aes_shift_rows op_i data_i).

(* Test bench checking that for a single step, the circuit and Coq semantics
   return the same result *)
Section SimpleTestBench.
  Definition aes_shift_rows_simple_inputs : list _ :=
    [(false, fromNatVec test_state)].

  (* Compute the expected outputs from the Coq/Cava semantics. *)
  Definition aes_shift_rows_simple_expected_outputs :=
    simulate (Comb (fun '(op_i, data_i) => aes_shift_rows op_i data_i))
             aes_shift_rows_simple_inputs.
End SimpleTestBench.

(* Test bench checking against full FIPS AES-256 encryption test vector *)
Section FIPSEncryptTestBench.
  Definition aes_shift_rows_enc_tb_inputs :=
    Eval vm_compute in
      (map (fun v => (false, from_flat v))
           (get_state_inputs ShiftRows fips_c3_forward)).

  Definition aes_shift_rows_enc_expected_outputs :=
    Eval vm_compute in
      (map from_flat (get_state_outputs ShiftRows fips_c3_forward)).
End FIPSEncryptTestBench.

(* Test bench checking against full FIPS AES-256 decryption test vector (for
   equivalent inverse cipher) *)
Section FIPSDecryptTestBench.
  Definition aes_shift_rows_dec_tb_inputs :=
    Eval vm_compute in
      (map (fun v => (true, from_flat v))
           (get_state_inputs InvShiftRows fips_c3_equivalent_inverse)).

  Definition aes_shift_rows_dec_expected_outputs :=
    Eval vm_compute in
      (map from_flat (get_state_outputs InvShiftRows fips_c3_equivalent_inverse)).
End FIPSDecryptTestBench.

(* Concatenate inputs from all tests *)
Definition aes_shift_rows_tb_all_inputs :=
  Eval vm_compute in
    (aes_shift_rows_simple_inputs
       ++ aes_shift_rows_enc_tb_inputs
       ++ aes_shift_rows_dec_tb_inputs)%list.

(* Concatenate expected outputs from all tests *)
Definition aes_shift_rows_tb_all_expected_outputs :=
  Eval vm_compute in
    (aes_shift_rows_simple_expected_outputs
       ++ aes_shift_rows_enc_expected_outputs
       ++ aes_shift_rows_dec_expected_outputs)%list.

Definition aes_shift_rows_tb :=
  testBench "aes_shift_rows_tb"
            aes_shift_rows_Interface
            aes_shift_rows_tb_all_inputs
            aes_shift_rows_tb_all_expected_outputs.
