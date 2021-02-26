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
Require Import AesSpec.AES256.
Require Import AesSpec.Tests.Common.
Require Import AesSpec.Tests.TestVectors.
Require Import AcornAes.AddRoundKeyCircuit.
Require Import AcornAes.Pkg.
Local Open Scope vector_scope.

(* add_round_key is internal to aes_cipher_core in OpenTitan and so does not have
* an "official" interface.
  https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_cipher_core.sv
*)
Definition aes_add_round_key_Interface :=
  combinationalInterface "aes_add_round_key"
  [ mkPort "key_i" (Vec (Vec (Vec Bit 8) 4) 4);
    mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)]
  [].

Definition aes_add_round_key_Netlist :=
  makeCircuitNetlist aes_add_round_key_Interface
                     (Comb (fun '(k,st) => aes_add_round_key k st)).

(* Test bench checking that for a single add_round_key, the circuit and Coq
   semantics return the same result *)
Section SimpleTestBench.
  (* Compute the expected outputs from the Coq/Cava semantics. *)
  Definition aes_add_round_key_simple_expected_outputs : seqType (Vec (Vec (Vec Bit 8) 4) 4)
    := simulate (Comb (fun '(key_i, data_i) => aes_add_round_key key_i data_i))
                 [(fromNatVec test_key, fromNatVec test_state)].

  Definition aes_add_round_key_simple_tb :=
    testBench "aes_add_round_key_simple_tb"
              aes_add_round_key_Interface
              [(fromNatVec test_key, fromNatVec test_state)]
              aes_add_round_key_simple_expected_outputs.
End SimpleTestBench.

(* Test bench checking against full FIPS AES-256 encryption test vector *)
Section FIPSEncryptTestBench.
  Definition aes_add_round_key_enc_tb_inputs :=
    Eval vm_compute in
      (combine (map from_flat (round_ksch fips_c3_forward))
               (map from_flat (get_state_inputs AddRoundKey fips_c3_forward))).

  Definition aes_add_round_key_enc_expected_outputs :=
    Eval vm_compute in
      (map from_flat (get_state_outputs AddRoundKey fips_c3_forward)).

  Definition aes_add_round_key_enc_tb
    := testBench "aes_add_round_key_enc_tb" aes_add_round_key_Interface
                 aes_add_round_key_enc_tb_inputs
                 aes_add_round_key_enc_expected_outputs.
End FIPSEncryptTestBench.

(* Test bench checking against full FIPS AES-256 decryption test vector (for
   equivalent inverse cipher) *)
Section FIPSDecryptTestBench.
  Definition aes_add_round_key_dec_tb_inputs :=
    Eval vm_compute in
      (combine (map from_flat (round_ksch fips_c3_equivalent_inverse))
               (map from_flat (get_state_inputs AddRoundKey fips_c3_equivalent_inverse))).

  Definition aes_add_round_key_dec_expected_outputs :=
    Eval vm_compute in
      (map from_flat (get_state_outputs AddRoundKey fips_c3_equivalent_inverse)).

  Definition aes_add_round_key_dec_tb
    := testBench "aes_add_round_key_dec_tb" aes_add_round_key_Interface
                 aes_add_round_key_dec_tb_inputs
                 aes_add_round_key_dec_expected_outputs.
End FIPSDecryptTestBench.
