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

(* This file has the top-level cipher definition and proofs, with all the
   subroutines instantiated. *)

Require Import Coq.Lists.List.
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.
Require Import AesSpec.AddRoundKey.
Require Import AesSpec.MixColumns.
Require Import AesSpec.ShiftRows.
Require Import AesSpec.SubBytes.
Require Import AesSpec.Cipher.
Require Import AesSpec.CommuteProperties.
Require Import AesSpec.StateTypeConversions.

Import StateTypeConversions.BigEndian.

Section Equivalence.
  Let state := Vector.t bool 128.
  Let round_key := Vector.t bool 128.
  Let bits_per_word := 32.
  Let Nb := 4%nat. (* From FIPS -- number of bytes per word *)
  Let Nr := 14%nat. (* From FIPS -- number of rounds *)

  Definition add_round_key (st : state) (k : round_key) : state :=
    let st := LittleEndian.to_cols_bits st in
    let k := LittleEndian.to_cols_bits k in
    LittleEndian.from_cols_bits (add_round_key bits_per_word Nb st k).

  Definition sub_bytes (st : state) : state :=
    from_list_rows (sub_bytes (to_list_rows st)).

  Definition shift_rows (st : state) : state :=
    from_list_rows (shift_rows (to_list_rows st)).

  Definition mix_columns (st : state) : state :=
    from_cols (mix_columns (to_cols st)).

  Definition inv_sub_bytes (st : state) : state :=
    from_list_rows (inv_sub_bytes (to_list_rows st)).

  Definition inv_shift_rows (st : state) : state :=
    from_list_rows (inv_shift_rows (to_list_rows st)).

  Definition inv_mix_columns (st : state) : state :=
    from_cols (inv_mix_columns (to_cols st)).

  Definition aes256_encrypt
             (first_key last_key : round_key) (middle_keys : list round_key)
             (input : state) : state :=
    cipher state round_key add_round_key sub_bytes shift_rows mix_columns
           first_key last_key middle_keys input.

  Definition aes256_decrypt
             (first_key last_key : round_key) (middle_keys : list round_key)
             (input : state) : state :=
    equivalent_inverse_cipher
      state round_key add_round_key inv_sub_bytes inv_shift_rows inv_mix_columns
      first_key last_key middle_keys input.

  Hint Rewrite @inverse_add_round_key @inverse_shift_rows @inverse_sub_bytes
       @inverse_mix_columns @sub_bytes_shift_rows_comm
       @inv_mix_columns_add_round_key_comm
       using solve [eauto] : inverse.

  Lemma aes256_decrypt_encrypt first_key last_key middle_keys input :
    aes256_decrypt last_key first_key (map inv_mix_columns (rev middle_keys))
                   (aes256_encrypt first_key last_key middle_keys input) = input.
  Proof.
    cbv [aes256_decrypt aes256_encrypt].
    eapply inverse_cipher_id; intros.
    all:cbv [add_round_key sub_bytes shift_rows mix_columns
                           inv_sub_bytes inv_shift_rows inv_mix_columns].
    all:autorewrite with conversions inverse.
    all:reflexivity.
  Qed.
End Equivalence.

Redirect "AES256_Assumptions" Print Assumptions aes256_decrypt_encrypt.

(* Specifications for OpenTitan circuits in terms of their exact state
   representation and arguments. *)
Section CircuitSpec.
  (* OpenTitan circuits expect row-major order with big-endian rows and columns
     and little-endan bytes. *)
  Definition from_flat st :=
    Vector.map (Vector.map (fun r => byte_to_bitvec r)) (BigEndian.to_rows st).
  Definition to_flat st :=
    BigEndian.from_rows (Vector.map (Vector.map (fun r => bitvec_to_byte r)) st).

  Definition aes_mix_columns_circuit_spec
             (op_i : bool) (state : Vector.t (Vector.t (Vector.t bool 8) 4) 4)
  : Vector.t (Vector.t (Vector.t bool 8) 4) 4 :=
    if op_i
    then from_flat (AES256.inv_mix_columns (to_flat state))
    else from_flat (AES256.mix_columns (to_flat state)).
End CircuitSpec.
