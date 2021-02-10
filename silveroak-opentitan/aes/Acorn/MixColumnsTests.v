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
Require Import AesSpec.Tests.CipherTest.
Require Import AcornAes.MixColumnsCircuit.
Require Import AcornAes.Pkg.
Import Pkg.Notations.

(* Test against FIPS test vectors *)
Section FIPSTests.
  (* Create a version of AES with the mix_columns circuit plugged in *)
  Let impl : AESStep -> Vector.t bool 128 -> Vector.t bool 128 -> Vector.t bool 128 :=
    (fun step key =>
       match step with
       | MixColumns =>
         fun st =>
           let input := from_flat st in
           let output := unIdent (aes_mix_columns [false] [input]) in
           to_flat (List.hd (defaultCombValue _) output)
       | InvMixColumns =>
         fun st =>
           let input := from_flat st in
           let output := unIdent (aes_mix_columns [true] [input]) in
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

Definition mixColTest1ExpectedOutput : Vector.t (Vector.t nat 4) 4
  := [[142; 77; 161; 188];
      [159; 220; 88; 157];
      [1; 1; 1; 1];
      [77; 126; 189; 248]]%vector.

(*** First work with MixCols.mix_cols spec. ***)

(* Test case from the first four rows of the Wikipedia page on AES mix_columns:
     https://en.wikipedia.org/wiki/Rijndael_MixColumns
*)
Definition mixColTest1InputNat : Vector.t (Vector.t nat 4) 4
  := [[219; 19; 83; 69];
      [242; 10; 34; 92];
      [1; 1; 1; 1];
      [45; 38; 49; 76]
  ]%vector.

Definition mixColTestInputs' : Vector.t (Vector.t Byte.byte 4) 4 := fromNatState mixColTest1InputNat.

Definition s1 : Vector.t (Vector.t Byte.byte 4) 4 := MixColumns.mix_columns mixColTestInputs'.

Example test_core_mix_cols : toNatState s1 = mixColTest1ExpectedOutput.
Proof. vm_compute. reflexivity. Qed.

(*** Second check with AES256.aes_mix_columns_top_spec. *)

Definition i1 := fromNatVec (transpose mixColTest1InputNat).
Definition s2 := transpose (AES256.aes_mix_columns_circuit_spec false i1).

Example test_aes_spec : toNatVec s2 = mixColTest1ExpectedOutput.
Proof. vm_compute. reflexivity. Qed.

(* A test now with the circuit. *)

Local Open Scope list_scope.

Definition r1L : list (Vector.t (Vector.t (Vector.t bool 8) 4) 4) := combinational (aes_mix_columns [false] [i1]).
Definition o1 := List.hd (defaultCombValue (Vec (Vec (Vec Bit 8) 4) 4)) r1L.

Local Open Scope vector_scope.

Example check_mix_cols_circuit : transpose (toNatVec o1) = mixColTest1ExpectedOutput.
Proof. vm_compute. reflexivity. Qed.
