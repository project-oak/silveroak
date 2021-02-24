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
Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.IdentityNew.
Require Import Cava.Acorn.Multistep.

Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AesSpec.CipherProperties.
Require Import AesSpec.ExpandAllKeys.
Require Import AcornAes.AddRoundKeyCircuit.
Require Import AcornAes.ShiftRowsCircuit.
Require Import AcornAes.SubBytesCircuit.
Require Import AcornAes.SubBytesEquivalenceNew.
Require Import AcornAes.MixColumnsCircuit.
Require Import AcornAes.CipherNewLoop.
Require Import AcornAes.CipherEquivalenceNew.
Import ListNotations.
Import Pkg.Notations.
Import StateTypeConversions.LittleEndian.

Local Notation round_constant := (Vec Bit 8) (only parsing).
Local Notation round_index := (Vec Bit 4) (only parsing).

Axiom key_expand : forall {signal} {semantics : Cava signal},
    signal Bit -> signal round_index -> signal key * signal round_constant ->
    cava (signal key * signal round_constant).
Axiom key_expand_spec : nat -> t bool 128 * t bool 8 -> t bool 128 * t bool 8.
Axiom inv_key_expand_spec : nat -> t bool 128 * t bool 8 -> t bool 128 * t bool 8.

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

Axiom add_round_key_equiv :
  forall (st : combType state) (k : combType key),
    unIdent (aes_add_round_key k st)
    = AES256.aes_add_round_key_circuit_spec k st.

Axiom shift_rows_equiv :
  forall (is_decrypt : bool) (st : combType state),
    unIdent (aes_shift_rows is_decrypt st)
    = AES256.aes_shift_rows_circuit_spec is_decrypt st.

Axiom mix_columns_equiv :
  forall (is_decrypt : bool) (st : combType state),
    unIdent (aes_mix_columns is_decrypt st)
    = AES256.aes_mix_columns_circuit_spec is_decrypt st.

Axiom key_expand_equiv :
  forall (is_decrypt : bool) (round_i : t bool 4) (k : t (t (t bool 8) 4) 4) (rcon : t bool 8),
    combinational (key_expand is_decrypt round_i (k, rcon))
    = let spec := if is_decrypt then inv_key_expand_spec else key_expand_spec in
      let kr := spec (N.to_nat (Bv2N round_i)) (flatten_key (k, rcon)) in
      (from_flat (fst kr), snd kr).

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
  | |- context [unIdent (aes_add_round_key _ _) = _] =>
    eapply add_round_key_equiv
  | |- context [unIdent (aes_sub_bytes _ _) = _] =>
    eapply sub_bytes_equiv
  | |- context [unIdent (aes_shift_rows _ _) = _] =>
    eapply shift_rows_equiv
  | |- context [unIdent (aes_mix_columns _ _) = _] =>
    eapply mix_columns_equiv
  | |- context [unIdent (key_expand ?is_decrypt _ _) = _] =>
    rewrite key_expand_equiv; cbv zeta;
    destruct is_decrypt; reflexivity
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
  multistep key_expand cipher_input = init_key :: middle_keys ++ [last_key] ->
  forall d,
    nth Nr (multistep (full_cipher key_expand) cipher_input) d
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
          || rewrite map_map; eapply ListUtils.map_id_ext; intros;
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
  let ciphertext := nth Nr (multistep (full_cipher key_expand) cipher_input_fwd) d in
  cipher_input_inv = make_cipher_signals Nr true init_key_input_inv
                                         (ciphertext :: init_state_ignored_inv) ->
  (* inverse key expansion reverses key expansion *)
  multistep key_expand cipher_input_fwd = rev (multistep key_expand cipher_input_inv) ->
  nth Nr (multistep (full_cipher key_expand) cipher_input_inv) d = plaintext.
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
  lazymatch goal with H : multistep key_expand _ = _ |- _ =>
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

(* TODO:uncomment once old version of this file is removed *)
(*
Redirect "FullCipherEquiv_Assumptions" Print Assumptions full_cipher_equiv.
Redirect "FullCipherInverse_Assumptions" Print Assumptions full_cipher_inverse.
*)
