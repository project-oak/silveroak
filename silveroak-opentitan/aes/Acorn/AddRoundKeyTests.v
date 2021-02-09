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

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.


Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import AesSpec.AES256.
Require Import AesSpec.Tests.Common.
Require Import AesSpec.Tests.CipherTest.
Require Import AcornAes.AddRoundKeyCircuit.
Require Import AcornAes.Pkg.

(* Test against FIPS test vectors *)
Section FIPSTests.
  (* Create a version of AES with the add_round_key circuit plugged in *)
  Let impl : AESStep -> Vector.t bool 128 -> Vector.t bool 128 -> Vector.t bool 128 :=
    (fun step key =>
       match step with
       | AddRoundKey =>
         fun st =>
           let input := from_flat st in
           let k := from_flat key in
           let output := unIdent (add_round_key [k]%list [input]%list) in
           to_flat (List.hd (defaultCombValue _) output)
       | _ => aes_impl step key
       end).

  (* encryption test *)
  Goal (aes_test_encrypt Matrix impl = Success).
  Proof. vm_compute. reflexivity. Qed.

  (* decryption test *)
  Goal (aes_test_decrypt Matrix impl = Success).
  Proof. vm_compute. reflexivity. Qed.
End FIPSTests.

Local Open Scope vector_scope.

(* add_round_key is internal to aes_cipher_core in OpenTitan and so does not have
* an "official" interface.
  https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_cipher_core.sv
*)
Definition add_round_key_Interface :=
  combinationalInterface "aes_add_round_key"
  [ mkPort "key_i" (Vec (Vec (Vec Bit 8) 4) 4);
    mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)]
  [].

Definition aes_add_round_key_Netlist
  := makeNetlist add_round_key_Interface (fun '(key_i, data_i) => add_round_key key_i data_i).

Definition test_state
  := [[219; 19; 83; 69];
      [242; 10; 34; 92];
      [1; 1; 1; 1];
      [45; 38; 49; 76]
  ].
Definition test_key
  := [[219; 19; 83; 69];
      [242; 10; 34; 92];
      [1; 1; 1; 1];
      [45; 38; 49; 76]
  ].

Local Open Scope list_scope.

(* Compute the expected outputs from the Coq/Cava semantics. *)
Definition add_round_key_expected_outputs : seqType (Vec (Vec (Vec Bit 8) 4) 4)
  := combinational (add_round_key [fromNatVec test_key] [fromNatVec test_state]).

Definition aes_add_round_key_tb :=
  testBench "aes_add_round_key_tb"
            add_round_key_Interface
            [(fromNatVec test_key, fromNatVec test_state)]
            add_round_key_expected_outputs.
