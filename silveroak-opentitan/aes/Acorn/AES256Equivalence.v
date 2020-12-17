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
Require Import ExtLib.Structures.Monads.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.MonadFacts.
Require Import Cava.Acorn.Identity.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AesSpec.CipherProperties.
Require Import AcornAes.AddRoundKey.
Require Import AcornAes.AddRoundKeyEquivalence.
Require Import AcornAes.CipherRound.
Require Import AcornAes.CipherEquivalence.
Require Import AcornAes.Common.
Import Common.Notations.

Axiom sub_bytes : forall {signal} {semantics : Cava signal} {monad : Monad cava},
    signal Bit -> signal state -> cava (signal state).
Axiom shift_rows : forall {signal} {semantics : Cava signal} {monad : Monad cava},
    signal Bit -> signal state -> cava (signal state).
Axiom mix_columns : forall {signal} {semantics : Cava signal} {monad : Monad cava},
    signal Bit -> signal state -> cava (signal state).

Axiom sub_bytes_equiv :
 forall st : t bool 128,
   from_cols_bitvecs
     (combinational (sub_bytes false (to_cols_bitvecs st))) = AES256.sub_bytes st.
Axiom shift_rows_equiv :
  forall st : t bool 128,
    from_cols_bitvecs
      (combinational (shift_rows false (to_cols_bitvecs st))) = AES256.shift_rows st.
Axiom mix_columns_equiv :
  forall st : t bool 128,
    from_cols_bitvecs
      (combinational (mix_columns false (to_cols_bitvecs st))) = AES256.mix_columns st.
Axiom inv_sub_bytes_equiv :
 forall st : t bool 128,
   from_cols_bitvecs
     (combinational (sub_bytes true (to_cols_bitvecs st))) = inv_sub_bytes st.
Axiom inv_shift_rows_equiv :
  forall st : t bool 128,
    from_cols_bitvecs
      (combinational (shift_rows true (to_cols_bitvecs st))) = inv_shift_rows st.
Axiom inv_mix_columns_equiv :
  forall st : t bool 128,
    from_cols_bitvecs
      (combinational (mix_columns true (to_cols_bitvecs st))) = inv_mix_columns st.

Hint Resolve add_round_key_equiv sub_bytes_equiv shift_rows_equiv
     mix_columns_equiv inv_sub_bytes_equiv inv_shift_rows_equiv
     inv_mix_columns_equiv : subroutines_equiv.

Definition full_cipher {signal} {semantics : Cava signal} {monad : Monad cava}
  : signal Bit -> signal key -> signal key -> list (signal key) -> signal state
    -> cava (signal state) :=
  cipher sub_bytes shift_rows mix_columns add_round_key.

Lemma full_cipher_equiv
      (is_decrypt : bool)
      (first_key last_key : combType key) (middle_keys : list (combType key))
      (input : combType state) :
  combinational
    (full_cipher is_decrypt first_key last_key middle_keys input)
  = to_cols_bitvecs
      ((if is_decrypt then aes256_decrypt else aes256_encrypt)
         (from_cols_bitvecs first_key) (from_cols_bitvecs last_key)
         (List.map from_cols_bitvecs middle_keys) (from_cols_bitvecs input)).
Proof.
  cbv [full_cipher].

  destruct is_decrypt.
  { (* decryption *)
    rewrite inverse_cipher_equiv. cbv [aes256_decrypt].

    (* Change key and state representations so they match *)
    erewrite equivalent_inverse_cipher_change_state_rep
      by eapply to_cols_bitvecs_from_cols_bitvecs.
    erewrite equivalent_inverse_cipher_change_key_rep
      with (projkey:=to_cols_bitvecs)
           (middle_keys_alt:=List.map from_cols_bitvecs middle_keys)
      by (apply to_cols_bitvecs_from_cols_bitvecs ||
          (rewrite List.map_map; apply ListUtils.map_id_ext;
           intros; autorewrite with conversions; reflexivity)).

    (* Prove that ciphers are equivalent because all subroutines are
       equivalent *)
    f_equal.
    eapply equivalent_inverse_cipher_subroutine_ext;
      eauto with subroutines_equiv. }
  { (* encryption *)
    rewrite cipher_equiv. cbv [aes256_encrypt].

    (* Change key and state representations so they match *)
    erewrite cipher_change_state_rep
      by eapply to_cols_bitvecs_from_cols_bitvecs.
    erewrite cipher_change_key_rep
      with (projkey:=to_cols_bitvecs)
           (middle_keys_alt:=List.map from_cols_bitvecs middle_keys)
      by (apply to_cols_bitvecs_from_cols_bitvecs ||
          (rewrite List.map_map; apply ListUtils.map_id_ext;
           intros; autorewrite with conversions; reflexivity)).

    (* Prove that ciphers are equivalent because all subroutines are
       equivalent *)
    f_equal.
    eapply cipher_subroutine_ext; eauto with subroutines_equiv. }
Qed.

Local Open Scope monad_scope.

Lemma decrypt_middle_keys_equiv (middle_keys : list (combType key)) :
  List.map (fun k => from_cols_bitvecs (combinational (mix_columns true k)))
           (List.rev middle_keys) =
  List.map inv_mix_columns (List.rev (List.map from_cols_bitvecs middle_keys)).
Proof.
  rewrite !List.map_rev. f_equal.
  rewrite List.map_map. apply List.map_ext; intro x.
  rewrite <-(to_cols_bitvecs_from_cols_bitvecs x).
  rewrite inv_mix_columns_equiv.
  autorewrite with conversions; reflexivity.
Qed.

Lemma full_cipher_inverse
      (first_key last_key : combType key) (middle_keys : list (combType key))
      (input : combType state) :
  let decrypt_middle_keys :=
      List.map (fun k => combinational (mix_columns true k)) (List.rev middle_keys) in
  combinational
    ((full_cipher false first_key last_key middle_keys >=>
      full_cipher true last_key first_key decrypt_middle_keys) input) = input.
Proof.
  cbv [mcompose]. simpl_ident.
  rewrite !full_cipher_equiv.
  autorewrite with conversions.
  rewrite List.map_map, decrypt_middle_keys_equiv.
  rewrite aes256_decrypt_encrypt.
  autorewrite with conversions.
  reflexivity.
Qed.

Redirect "FullCipherEquiv_Assumptions" Print Assumptions full_cipher_equiv.
Redirect "FullCipherInverse_Assumptions" Print Assumptions full_cipher_inverse.
