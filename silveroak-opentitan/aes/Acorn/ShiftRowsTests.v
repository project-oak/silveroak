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

Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import AesSpec.AES256.
Require Import AesSpec.Tests.Common.
Require Import AesSpec.Tests.CipherTest.
Require Import AcornAes.ShiftRowsCircuit.

(* Test against FIPS test vectors *)
Section FIPSTests.
  (* Create a version of AES with the shift_rows circuit plugged in *)
  Let impl : AESStep -> Vector.t bool 128 -> Vector.t bool 128 -> Vector.t bool 128 :=
    (fun step key =>
       match step with
       | ShiftRows =>
         fun st =>
           let input := from_flat st in
           let output := unIdent (aes_shift_rows false input) in
           to_flat output
       | InvShiftRows =>
         fun st =>
           let input := from_flat st in
           let output := unIdent (aes_shift_rows true input) in
           to_flat output
       | _ => aes_impl step key
       end).

  (* encryption test *)
  Goal (aes_test_encrypt Matrix impl = Success).
  Proof. vm_compute. reflexivity. Qed.

  (* decryption test *)
  Goal (aes_test_decrypt Matrix impl = Success).
  Proof. vm_compute. reflexivity. Qed.
End FIPSTests.
