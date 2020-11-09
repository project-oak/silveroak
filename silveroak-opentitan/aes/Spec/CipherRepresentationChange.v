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
Require Import Cava.ListUtils.
Require Import AesSpec.Cipher.

Section ChangeKeyRepresentation.
  Context (state key key_alt : Type)
          (projkey : key_alt -> key)
          (add_round_key : state -> key -> state)
          (sub_bytes shift_rows mix_columns : state -> state)
          (inv_sub_bytes inv_shift_rows inv_mix_columns : state -> state).

  Lemma cipher_change_key_rep first_key last_key middle_keys
        first_key_alt last_key_alt middle_keys_alt input :
    projkey first_key_alt = first_key ->
    projkey last_key_alt = last_key ->
    map projkey middle_keys_alt = middle_keys ->
    cipher state key add_round_key sub_bytes shift_rows mix_columns
           first_key last_key middle_keys input
    = cipher state key_alt (fun st k => add_round_key st (projkey k))
             sub_bytes shift_rows mix_columns first_key_alt last_key_alt
             middle_keys_alt input.
  Proof.
    intros; subst; cbv [cipher].
    repeat (f_equal; [ ]). rewrite fold_left_map.
    reflexivity.
  Qed.

  Lemma equivalent_inverse_cipher_change_key_rep first_key last_key middle_keys
        first_key_alt last_key_alt middle_keys_alt input :
    projkey first_key_alt = first_key ->
    projkey last_key_alt = last_key ->
    map projkey middle_keys_alt = middle_keys ->
    equivalent_inverse_cipher
      state key add_round_key
      inv_sub_bytes inv_shift_rows inv_mix_columns
      first_key last_key middle_keys input
    = equivalent_inverse_cipher
        state key_alt (fun st k => add_round_key st (projkey k))
        inv_sub_bytes inv_shift_rows inv_mix_columns first_key_alt last_key_alt
        middle_keys_alt input.
  Proof.
    intros; subst; cbv [equivalent_inverse_cipher].
    repeat (f_equal; [ ]). rewrite !fold_left_map.
    reflexivity.
  Qed.
End ChangeKeyRepresentation.
