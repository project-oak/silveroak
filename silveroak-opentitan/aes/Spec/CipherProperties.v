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
Require Import Cava.Util.List.
Require Import AesSpec.Cipher.

Section ChangeRepresentation.
  Context (state state_alt key key_alt : Type)
          (projkey : key_alt -> key)
          (to_state_alt : state -> state_alt)
          (from_state_alt : state_alt -> state)
          (add_round_key : state -> key -> state)
          (sub_bytes shift_rows mix_columns : state -> state)
          (inv_sub_bytes inv_shift_rows inv_mix_columns : state -> state).
  Context (from_state_alt_to_state_alt : forall st, from_state_alt (to_state_alt st) = st).

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

  Lemma cipher_change_state_rep first_key last_key middle_keys
        input :
    cipher state key add_round_key sub_bytes shift_rows mix_columns
           first_key last_key middle_keys input
    = from_state_alt
        (cipher state_alt key
                (fun st k => to_state_alt (add_round_key (from_state_alt st) k))
                (fun st => to_state_alt (sub_bytes (from_state_alt st)))
                (fun st => to_state_alt (shift_rows (from_state_alt st)))
                (fun st => to_state_alt (mix_columns (from_state_alt st)))
                first_key last_key middle_keys (to_state_alt input)).
  Proof.
    intros; subst; cbv [cipher].
    rewrite !from_state_alt_to_state_alt.
    repeat (f_equal; [ ]).
    factor_out_loops.
    eapply fold_left_double_invariant
      with (I:=fun b c => c = from_state_alt b);
      intros; subst;
        rewrite ?from_state_alt_to_state_alt;
        reflexivity.
  Qed.

  Lemma equivalent_inverse_cipher_change_state_rep first_key last_key middle_keys
        input :
    equivalent_inverse_cipher
      state key add_round_key inv_sub_bytes inv_shift_rows inv_mix_columns
      first_key last_key middle_keys input
    = from_state_alt
        (equivalent_inverse_cipher
           state_alt key
           (fun st k => to_state_alt (add_round_key (from_state_alt st) k))
           (fun st => to_state_alt (inv_sub_bytes (from_state_alt st)))
           (fun st => to_state_alt (inv_shift_rows (from_state_alt st)))
           (fun st => to_state_alt (inv_mix_columns (from_state_alt st)))
           first_key last_key middle_keys (to_state_alt input)).
  Proof.
    intros; subst; cbv [equivalent_inverse_cipher].
    rewrite !from_state_alt_to_state_alt.
    repeat (f_equal; [ ]).
    factor_out_loops.
    eapply fold_left_double_invariant
      with (I:=fun b c => c = from_state_alt b);
      intros; subst;
        rewrite ?from_state_alt_to_state_alt;
        reflexivity.
  Qed.
End ChangeRepresentation.

Section Extensionality.
  Context (state key : Type)
          (add_round_key add_round_key' : state -> key -> state)
          (sub_bytes shift_rows mix_columns : state -> state)
          (sub_bytes' shift_rows' mix_columns' : state -> state)
          (inv_sub_bytes inv_shift_rows inv_mix_columns : state -> state)
          (inv_sub_bytes' inv_shift_rows' inv_mix_columns' : state -> state).
  Context (add_round_key_equiv : forall st k, add_round_key st k = add_round_key' st k)
          (sub_bytes_equiv : forall st, sub_bytes st = sub_bytes' st)
          (shift_rows_equiv : forall st, shift_rows st = shift_rows' st)
          (mix_columns_equiv : forall st, mix_columns st = mix_columns' st)
          (inv_sub_bytes_equiv : forall st, inv_sub_bytes st = inv_sub_bytes' st)
          (inv_shift_rows_equiv : forall st, inv_shift_rows st = inv_shift_rows' st)
          (inv_mix_columns_equiv : forall st, inv_mix_columns st = inv_mix_columns' st).

  Hint Rewrite add_round_key_equiv sub_bytes_equiv shift_rows_equiv mix_columns_equiv
       inv_sub_bytes_equiv inv_shift_rows_equiv inv_mix_columns_equiv : equiv.

  Lemma cipher_subroutine_ext first_key last_key middle_keys input :
    cipher state key add_round_key sub_bytes shift_rows mix_columns
           first_key last_key middle_keys input
    = cipher state key add_round_key' sub_bytes' shift_rows' mix_columns'
             first_key last_key middle_keys input.
  Proof.
    cbv [cipher]. autorewrite with equiv.
    erewrite fold_left_ext; [ reflexivity | ].
    intros. autorewrite with equiv. reflexivity.
  Qed.

  Lemma equivalent_inverse_cipher_subroutine_ext
        first_key last_key middle_keys input :
    equivalent_inverse_cipher
      state key add_round_key inv_sub_bytes inv_shift_rows inv_mix_columns
      first_key last_key middle_keys input
    = equivalent_inverse_cipher
        state key add_round_key' inv_sub_bytes' inv_shift_rows' inv_mix_columns'
        first_key last_key middle_keys input.
  Proof.
    cbv [equivalent_inverse_cipher]. autorewrite with equiv.
    erewrite fold_left_ext; [ reflexivity | ].
    intros. autorewrite with equiv. reflexivity.
  Qed.

End Extensionality.
