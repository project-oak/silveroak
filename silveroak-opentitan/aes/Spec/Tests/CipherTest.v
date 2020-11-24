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
Require Import AesSpec.Placeholder.MixColumns.
Require Import AesSpec.Placeholder.Sbox.
Require Import AesSpec.Placeholder.ShiftRows.
Require Import AesSpec.Placeholder.SubBytes.
Require Import AesSpec.AddRoundKey.
Local Open Scope string_scope.

Local Notation byte := Byte.byte (only parsing).
Local Notation round_key := (Vector.t bool 128) (only parsing).
Local Notation state := (Vector.t bool 128) (only parsing).
Local Notation bytes_per_word := 4%nat.
Local Notation bits_per_word := (bytes_per_word * 8)%nat.
Local Notation Nb := 4%nat.

(* Conversions between different representations of the state *)
Section Conversions.
  (* Notes on representation:

     Everything in FIPS is big-endian, while Coq's native bitvectors are
     little-endian. The flat bit-vector for the state is therefore
     little-endian, while rows/columns created from it use the big-endian
     representation.

     For interpretation as a 2-D matrix, bytes in the flat representation are in
     *column-major* order (see FIPS 197 Fig. 3) *)

  Definition to_big_endian_bytes (st : state) : Vector.t byte (bytes_per_word * Nb) :=
    (* byte conversion expects little-endian form *)
    let bytes := bitvec_to_bytevec (bytes_per_word * Nb) st in
    (* reverse to get big-endian *)
    reverse bytes.
  Definition from_big_endian_bytes (bytes : Vector.t byte (bytes_per_word * Nb)) : state :=
    let bytes := reverse bytes in (* change to little-endian *)
    (* byte conversion expects little-endian form *)
    bytevec_to_bitvec _ bytes.

  (* Convert 1-D state to/from 2-D arrays *)
  Definition to_cols (st : state) : Vector.t (Vector.t byte bytes_per_word) Nb :=
    reshape (to_big_endian_bytes st).
  Definition to_rows (st : state) : Vector.t (Vector.t byte Nb) bytes_per_word :=
    transpose (to_cols st).
  Definition from_rows (v : Vector.t (Vector.t byte Nb) bytes_per_word) : state :=
    from_big_endian_bytes (flatten (transpose v)).
  Definition from_cols (v : Vector.t (Vector.t byte bytes_per_word) Nb) : state :=
    from_big_endian_bytes (flatten v).

  (* Convert state to/from columns, but such that columns are bits (still
     big-endian) instead of bytes *)
  Definition to_cols_bits (st : state) : Vector.t (Vector.t bool bits_per_word) Nb :=
    let cols := to_cols st in
    (* byte conversion expects little-endian form, so reverse each column and
       then reverse back *)
    map (fun c => reverse (bytevec_to_bitvec _ (reverse c))) cols.
  Definition from_cols_bits (bits : Vector.t (Vector.t bool bits_per_word) Nb)
    : state := from_cols (map (fun c => reverse (bitvec_to_bytevec _ (reverse c))) bits).

  (* Convert state to/from rows, but as lists instead of vectors *)
  Definition to_list_rows (st : state) : list (list Byte.byte) :=
    to_list (map to_list (to_rows st)).
  Definition from_list_rows (rows : list (list Byte.byte)) : state :=
    let rows := List.map (of_list_sized Byte.x00 bytes_per_word) rows in
    let rows := of_list_sized (Vector.const Byte.x00 _) Nb rows in
    from_rows rows.
End Conversions.

Definition add_round_key (k : round_key) (st : state) : state :=
  let st := to_cols_bits st in
  let k := to_cols_bits k in
  from_cols_bits (add_round_key bits_per_word Nb st k).

Definition sub_bytes (st : state) : state :=
  from_cols (sub_bytes forward_sbox (to_cols st)).

Definition shift_rows (st : state) : state :=
  from_list_rows (shift_rows Nb (to_list_rows st)).

Definition mix_columns (st : state) : state :=
  from_cols (mix_columns (to_cols st)).

Definition inv_sub_bytes (st : state) : state :=
  from_cols (SubBytes.sub_bytes inverse_sbox (to_cols st)).

Definition inv_shift_rows (st : state) : state :=
  from_list_rows (inv_shift_rows Nb (to_list_rows st)).

Definition inv_mix_columns (st : state) : state :=
  from_cols (inv_mix_columns (to_cols st)).

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
Proof. native_compute. reflexivity. Qed.
Goal (aes_test_decrypt Hex aes_impl = Success).
Proof. native_compute. reflexivity. Qed.
