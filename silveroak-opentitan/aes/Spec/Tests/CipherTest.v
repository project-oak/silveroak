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

Require Import Coq.Vectors.Vector.
Require Import Coq.Strings.String.
Require Import Cava.BitArithmetic.
Require Import Cava.VectorUtils.
Require Import AesSpec.Tests.Common.
Require Import AesSpec.Tests.TestVectors.
Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Local Open Scope string_scope.

Local Notation byte := Byte.byte (only parsing).
Local Notation round_key := (Vector.t bool 128) (only parsing).
Local Notation state := (Vector.t bool 128) (only parsing).
Local Notation bytes_per_word := 4%nat.
Local Notation bits_per_word := (bytes_per_word * 8)%nat.
Local Notation Nb := 4%nat.

Definition aes_impl (step : AESStep) (k : round_key) : state -> state :=
  match step with
  | AddRoundKey => add_round_key k
  | MixColumns => mix_columns
  | SubBytes => sub_bytes
  | ShiftRows => shift_rows
  | InvMixColumns => inv_mix_columns
  | InvSubBytes => inv_sub_bytes
  | InvShiftRows => inv_shift_rows
  end.

Definition state_eqb (s1 s2 : state): bool :=
  if Vector.eq_dec _ Bool.eqb Bool.eqb_true_iff _ s1 s2
  then true
  else false.

(* Print state as matrix for easier debugging *)
Definition print_matrix (st : state) : string :=
  let rows := to_rows st in
  let lines :=
      Vector.map (fun r =>
                    String.concat
                      " | " (to_list
                               (Vector.map (fun b => Bv2Hex (byte_to_bitvec b)) r)))
                 rows in
  newline ++ String.concat newline (to_list lines).

(* Selects how to print the state in errors *)
Inductive TestPrintFormat := Hex | Matrix.

(* Shortcut/convenience definitions *)
Definition aes_test_encrypt
           (fmt : TestPrintFormat)
           (impl : AESStep -> round_key -> state -> state) : TestResult :=
  let test := fips_c3_forward in
  match fmt with
  | Matrix => run_test state_eqb print_matrix print_matrix test impl
  | Hex => run_test state_eqb Bv2Hex Bv2Hex test impl
  end.

Definition aes_test_decrypt
           (fmt : TestPrintFormat)
           (impl : AESStep -> round_key -> state -> state) : TestResult :=
  let test := fips_c3_equivalent_inverse in
  match fmt with
  | Matrix => run_test state_eqb print_matrix print_matrix test impl
  | Hex => run_test state_eqb Bv2Hex Bv2Hex test impl
  end.

Goal (aes_test_encrypt Hex aes_impl = Success).
Proof. vm_compute. reflexivity. Qed.
Goal (aes_test_decrypt Hex aes_impl = Success).
Proof. vm_compute. reflexivity. Qed.
