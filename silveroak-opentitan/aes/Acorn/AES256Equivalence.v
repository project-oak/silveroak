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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import coqutil.Tactics.destr.
Require Import ExtLib.Structures.Monads.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.Vector.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Core.Circuit.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.Simulation.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AesSpec.CipherProperties.
Require Import AesSpec.ExpandAllKeys.
Require Import AcornAes.AddRoundKeyCircuit.
Require Import AcornAes.AddRoundKeyEquivalence.
Require Import AcornAes.ShiftRowsCircuit.
Require Import AcornAes.ShiftRowsEquivalence.
Require Import AcornAes.SubBytesCircuit.
Require Import AcornAes.SubBytesEquivalence.
Require Import AcornAes.MixColumnsCircuit.
Require Import AcornAes.MixColumnsEquivalence.
Require Import AcornAes.CipherCircuit.
Require Import AcornAes.CipherEquivalence.
Import ListNotations.
Import Pkg.Notations.
Import StateTypeConversions.LittleEndian.

Local Notation round_constant := (Vec Bit 8) (only parsing).
Local Notation round_index := (Vec Bit 4) (only parsing).

(* convenience definition for converting to/from flat keys in key * round
   constant pairs *)
Definition flatten_key (kr : combType key * combType round_constant)
  : t bool 128 * combType round_constant := (to_flat (fst kr), snd kr).
Definition unflatten_key (kr : t bool 128 * combType round_constant)
  : combType key * combType round_constant := (from_flat (fst kr), snd kr).
Lemma flatten_unflatten kr : flatten_key (unflatten_key kr) = kr.
Proof.
  cbv [flatten_key unflatten_key]. destruct kr; cbn [fst snd].
  autorewrite with conversions. reflexivity.
Qed.
Lemma unflatten_flatten kr : unflatten_key (flatten_key kr) = kr.
Proof.
  cbv [flatten_key unflatten_key]. destruct kr; cbn [fst snd].
  autorewrite with conversions. reflexivity.
Qed.
Hint Rewrite @unflatten_flatten @flatten_unflatten using solve [eauto] : conversions.

Hint Resolve add_round_key_equiv sub_bytes_equiv shift_rows_equiv
     mix_columns_equiv : subroutines_equiv.

Definition full_cipher {signal} {semantics : Cava signal}
           key_expand
  : Circuit
      (signal Bit * signal round_index * signal round_index * signal round_index
       * signal key * signal state)
      (signal state) :=
  cipher
    aes_sub_bytes aes_shift_rows aes_mix_columns aes_add_round_key
    (fun k => aes_mix_columns one k) (* Hard-wire is_decrypt to '1' *)
    key_expand.

Local Ltac solve_side_conditions :=
  cbv zeta; intros;
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- context [aes_add_round_key _ _ = _] =>
    eapply add_round_key_equiv
  | |- context [aes_sub_bytes _ _ = _] =>
    eapply sub_bytes_equiv
  | |- context [aes_shift_rows _ _ = _] =>
    eapply shift_rows_equiv
  | |- context [aes_mix_columns _ _ = _] =>
    eapply mix_columns_equiv
  | |- context [_ < 2 ^ 4] => change (2 ^ 4)%nat with 16; Lia.lia
  | |- map fst (all_keys _ _ _) = _ => solve [eauto]
  | |- length _ = _ => length_hammer
  | |- hd _ _ = _ => reflexivity
  | _ => solve [eauto]
  end.

Lemma full_cipher_equiv
      (is_decrypt : bool) key_expand init_key_input init_state_ignored
      (init_key last_key : combType key)
      (middle_keys : list (combType key)) (init_state : combType state)
      (cipher_input : list _):
  let Nr := 14 in
  let middle_keys_flat :=
      if is_decrypt
      then List.map AES256.inv_mix_columns (List.map to_flat middle_keys)
      else List.map to_flat middle_keys in
  length init_key_input = S Nr ->
  length init_state_ignored = Nr ->
  length middle_keys = Nr - 1 ->
  cipher_input = make_cipher_signals Nr is_decrypt init_key_input
                                     (init_state :: init_state_ignored) ->
  (* precomputed keys match key expansion *)
  simulate key_expand cipher_input = init_key :: middle_keys ++ [last_key] ->
  forall d,
    nth Nr (simulate (full_cipher key_expand) cipher_input) d
    = from_flat
        ((if is_decrypt then aes256_decrypt else aes256_encrypt)
           (to_flat init_key) (to_flat last_key) middle_keys_flat
           (to_flat init_state)).
Proof.
  cbv [full_cipher]; intros.
  erewrite cipher_equiv by solve_side_conditions.
  cbv [aes256_decrypt aes256_encrypt].
  destruct is_decrypt.
  { (* make key/state representations match *)
    erewrite equivalent_inverse_cipher_change_state_rep
      by eapply from_flat_to_flat. apply f_equal.
    rewrite <-map_map with (g:=from_flat).
    erewrite equivalent_inverse_cipher_change_key_rep
      by (eapply from_flat_to_flat || reflexivity).
    rewrite !map_map.
    (* equivalent because all subroutines are equivalent *)
    eapply equivalent_inverse_cipher_subroutine_ext;
      intros; autounfold with circuit_specs;
        autorewrite with conversions; try reflexivity. }
  { (* make key/state representations match *)
    erewrite cipher_change_state_rep
      by eapply from_flat_to_flat. apply f_equal.
    erewrite cipher_change_key_rep
      with (middle_keys_alt:=map to_flat middle_keys)
      by (eapply from_flat_to_flat
          || rewrite map_map; eapply List.map_id_ext; intros;
          autorewrite with conversions; reflexivity).
    (* equivalent because all subroutines are equivalent *)
    eapply cipher_subroutine_ext;
      intros; autounfold with circuit_specs;
        autorewrite with conversions; try reflexivity. }
Qed.

Lemma full_cipher_inverse
      (is_decrypt : bool) key_expand
      init_key_input_fwd init_key_input_inv
      init_state_ignored_fwd init_state_ignored_inv
      cipher_input_fwd cipher_input_inv
      (plaintext : combType state) d :
  let Nr := 14 in
  length init_key_input_fwd = S Nr ->
  length init_key_input_inv = S Nr ->
  length init_state_ignored_fwd = Nr ->
  length init_state_ignored_inv = Nr ->
  cipher_input_fwd = make_cipher_signals Nr false init_key_input_fwd
                                         (plaintext :: init_state_ignored_fwd) ->
  let ciphertext := nth Nr (simulate (full_cipher key_expand) cipher_input_fwd) d in
  cipher_input_inv = make_cipher_signals Nr true init_key_input_inv
                                         (ciphertext :: init_state_ignored_inv) ->
  (* inverse key expansion reverses key expansion *)
  simulate key_expand cipher_input_fwd = rev (simulate key_expand cipher_input_inv) ->
  nth Nr (simulate (full_cipher key_expand) cipher_input_inv) d = plaintext.
Proof.
  intros. simpl_ident. subst_lets.

  (* we need a default value of key for some later rewrites *)
  assert (combType key) as default_key
      by (destruct init_key_input_fwd; [ cbn [length] in *; length_hammer | eassumption ]).

  do 2
     (erewrite full_cipher_equiv;
      [ | lazymatch goal with
          | |- context [make_cipher_signals] => eassumption
          | |- _ = _ :: _ ++ [_] =>
            eapply eta_list_cons_snoc with (d0:=default_key); subst; length_hammer
          | _ => idtac
          end .. ];
      [ | subst; length_hammer .. ]).

  autorewrite with conversions.
  cbv [combType Bvector.Bvector] in *.
  lazymatch goal with H : simulate key_expand _ = _ |- _ =>
                      rewrite H end.
  let l := lazymatch goal with
             |- context [map inv_mix_columns ?l] =>
             l end in
  rewrite <-(rev_involutive l).
  autorewrite with pull_rev.
  rewrite <-!map_rev with (f:=inv_mix_columns).
  rewrite removelast_tl.
  rewrite aes256_decrypt_encrypt.
  autorewrite with conversions.
  reflexivity.
Qed.

Redirect "FullCipherEquiv_Assumptions" Print Assumptions full_cipher_equiv.
Redirect "FullCipherInverse_Assumptions" Print Assumptions full_cipher_inverse.
