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

(* TODO: these definitions need to be filled in once the mixcolumns spec is finalized *)
Axiom inverse_mix_columns :
  forall Nb (st : Vector.t _ Nb), inv_mix_columns (mix_columns st) = st.

Axiom mix_columns_add_round_key_comm :
  forall (st k : Vector.t _ 4),
    let to_bits x := LittleEndian.to_cols_bits (from_cols x) in
    let from_bits x := to_cols (LittleEndian.from_cols_bits x) in
    add_round_key 32 4
                  (to_bits (inv_mix_columns st))
                  (to_bits (inv_mix_columns k))
    = to_bits
        (inv_mix_columns
           (from_bits
              (add_round_key
                 32 4 (to_bits st) (to_bits k)))).

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

  (* Top level specifications of OpenTitan mix_columns sub-components. *)
  Definition aes_mix_columns_top_spec (op : bool) (i : Vector.t (Vector.t (Vector.t bool 8) 4) 4)
                                      : Vector.t (Vector.t (Vector.t bool 8) 4) 4 :=
    let i_bytes := Vector.map (Vector.map bitvec_to_byte) (transpose i) in
    let i_big := BigEndian.from_rows (transpose i_bytes) in
    let bytes_o := BigEndian.to_cols (mix_columns i_big) in
    Vector.map (Vector.map byte_to_bitvec) bytes_o.

  Hint Rewrite @inverse_add_round_key @inverse_shift_rows @inverse_sub_bytes
       @inverse_mix_columns @sub_bytes_shift_rows_comm @mix_columns_add_round_key_comm
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
