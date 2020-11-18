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
Require Import ExtLib.Structures.Monads.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.
Require Import Cava.Monad.MonadFacts.
Require Import Cava.Acorn.Acorn.

Require Import AesSpec.Cipher.
Require Import AcornAes.CipherRound.

Existing Instance Combinational.

Section WithSubroutines.
  Local Notation byte := (t bool 8).
  Local Notation state := (t (t byte 4) 4) (only parsing).
  Local Notation key := (t (t byte 4) 4) (only parsing).
  Context (sub_bytes:     state -> ident state)
          (shift_rows:    state -> ident state)
          (mix_columns:   state -> ident state)
          (add_round_key : key -> state -> ident state).

  Let sub_bytes' : state -> state := (fun st => unIdent (sub_bytes st)).
  Let shift_rows' : state -> state := (fun st => unIdent (shift_rows st)).
  Let mix_columns' : state -> state := (fun st => unIdent (mix_columns st)).
  (* Note: argument order is switched for spec *)
  Let add_round_key' : state -> key -> state :=
    (fun st k => unIdent (add_round_key k st)).

  Lemma cipher_equiv
        (first_key last_key : key) (middle_keys : list key) (input : state) :
    let cipher := (cipher sub_bytes shift_rows mix_columns add_round_key) in
    let cipher_spec := (Cipher.cipher _ _ add_round_key'
                                      sub_bytes' shift_rows' mix_columns') in
    unIdent (cipher first_key last_key middle_keys input)
    = cipher_spec first_key last_key middle_keys input.
  Proof.
    cbv zeta. subst sub_bytes' shift_rows' mix_columns' add_round_key'.
    cbv [cipher cipher_round Cipher.cipher]. cbn [mcompose bind ret Monad_ident unIdent].
    repeat (f_equal; [ ]). rewrite foldLM_ident_fold_left.
    eapply fold_left_preserves_relation; [ reflexivity | ].
    intros; subst. reflexivity.
  Qed.

  (* If we assume all the subroutines are the inverse operations, we get the
     equivalent inverse cipher *)
  Lemma inverse_cipher_equiv
        (first_key last_key : key) (middle_keys : list key) (input : state) :
    let cipher := (cipher sub_bytes shift_rows mix_columns add_round_key) in
    let cipher_spec := (Cipher.equivalent_inverse_cipher
                          _ _ add_round_key' sub_bytes' shift_rows' mix_columns') in
    unIdent (cipher first_key last_key middle_keys input)
    = cipher_spec first_key last_key middle_keys input.
  Proof.
    cbv zeta. subst sub_bytes' shift_rows' mix_columns' add_round_key'.
    cbv [cipher cipher_round Cipher.equivalent_inverse_cipher].
    cbn [mcompose bind ret Monad_ident unIdent].
    repeat (f_equal; [ ]). rewrite foldLM_ident_fold_left.
    eapply fold_left_preserves_relation; [ reflexivity | ].
    intros; subst. reflexivity.
  Qed.
End WithSubroutines.
