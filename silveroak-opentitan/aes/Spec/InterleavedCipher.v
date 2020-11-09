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
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope list_scope.

Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import AesSpec.Cipher.
Require Import AesSpec.ExpandAllKeys.

Section Spec.
  Context {state key : Type}
          (add_round_key : state -> key -> state)
          (sub_bytes shift_rows mix_columns : state -> state)
          (key_expand : nat -> key -> key).

  Definition cipher_round_interleaved
             (loop_state : key * state) (i : nat)
    : key * state :=
    let '(round_key, st) := loop_state in
    let st := if i =? 0
              then add_round_key st round_key
              else
                let st := sub_bytes st in
                let st := shift_rows st in
                let st := mix_columns st in
                let st := add_round_key st round_key in
                st in
    let round_key := key_expand i round_key in
    (round_key, st).

  (* AES cipher with interleaved key expansion and conditional for first round *)
  Definition cipher_interleaved
             (Nr : nat) (* number of rounds *)
             (initial_key : key)
             (input : state) : state :=
    let st := input in
    let loop_end_state :=
        fold_left cipher_round_interleaved
          (List.seq 0 Nr) (initial_key, st) in
    let '(last_key, st) := loop_end_state in
    let st := sub_bytes st in
    let st := shift_rows st in
    let st := add_round_key st last_key in
    st.

  Section Equivalence.
    Context (Nr : nat) (initial_key : key)
            (first_key : key) (middle_keys : list key) (last_key : key).
    Context (all_keys_eq :
               all_keys key_expand Nr initial_key
               = first_key :: middle_keys ++ [last_key]).

    Let cipher := cipher state key add_round_key sub_bytes shift_rows mix_columns.

    (* Interleaved cipher is equivalent to original cipher *)
    Lemma cipher_interleaved_equiv input :
      cipher_interleaved Nr initial_key input =
      cipher first_key last_key middle_keys input.
    Proof.
      intros. subst cipher.

      (* get the key *pairs* *)
      pose proof all_keys_eq as Hall_keys.

      cbv [cipher_interleaved cipher_round_interleaved Cipher.cipher].
      rewrite fold_left_to_seq with (default:=initial_key).
      pose proof (length_all_keys _ _ _ _ _ Hall_keys).
      autorewrite with push_length in *.

      (* Nr cannot be 0 *)
      destruct Nr as [|Nr_m1]; [ lia | ].
      pose proof (hd_all_keys _ _ _ _ _ Hall_keys ltac:(lia)).
      subst.
      match goal with
      | H : length ?x + 1 = S ?n |- context [length ?x] =>
        replace (length x) with n by lia
      end.

      (* extract first step from cipher_alt so loops are in sync *)
      cbn [List.seq fold_left]. rewrite Nat.eqb_refl.
      rewrite <-seq_shift, fold_left_map.

      (* state the relationship between the two loop states (invariant) *)
      lazymatch goal with
      | H : all_keys ?key_expand ?n ?k = _ |- _ =>
        pose (R:= fun (i : nat) (x : key * state) (y : state) =>
                    x = (nth (S i)
                             (all_keys key_expand n k) k, y))
      end.

      (* find loops on each side *)
      lazymatch goal with
      | |- ?LHS = ?RHS =>
        let lfold :=
            lazymatch LHS with
            | context [fold_left ?f ?ls ?b] => constr:(fold_left f ls b) end in
        let rfold :=
            lazymatch RHS with
            | context [fold_left ?f ?ls ?b] => constr:(fold_left f ls b) end in
        let H := fresh in
        (* assert that invariant is satisfied at the end of the loop *)
        assert (H: R Nr_m1 lfold rfold);
          [ | subst R; cbv beta in *; rewrite H ]
      end.
      2:{
        (* prove that if the invariant is satisfied at the end of the loop, the
           postcondition is true *)
        repeat destruct_pair_let.
        f_equal; [ ].
        rewrite Hall_keys, app_comm_cons.
        rewrite app_nth2 by length_hammer.
        match goal with |- context [nth ?i _ _] =>
                        replace i with 0 by length_hammer end.
        reflexivity. }

      (* use the fold_left invariant lemma *)
      apply fold_left_preserves_relation_seq with (R0:=R); subst R.
      { (* invariant holds at loop start *)
        cbv beta. rewrite nth_all_keys by lia.
        reflexivity. }
      { (* invariant holds through loop step *)
        cbv beta; intros; subst. repeat destruct_pair_let.
        rewrite Nat.eqb_compare; cbn [Nat.compare].
        f_equal;
          [ rewrite !nth_all_keys_succ by lia;
            reflexivity | ].
        f_equal; [ ].
        rewrite Hall_keys. cbn [nth].
        rewrite app_nth1 by length_hammer.
        reflexivity. }
    Qed.
  End Equivalence.

  (* assume key_expand and all subroutines are the *inverse* operations, and
     prove equivalent to inverse cipher *)
  Section InverseEquivalence.
    Context (Nr : nat) (initial_key : key)
            (first_key : key) (middle_keys : list key) (last_key : key).
    Context (all_keys_eq :
               all_keys key_expand Nr initial_key
               = first_key :: middle_keys ++ [last_key]).

    Let inverse_cipher :=
      equivalent_inverse_cipher
        state key add_round_key sub_bytes shift_rows mix_columns.

    (* Interleaved cipher is equivalent to original cipher *)
    Lemma inverse_cipher_interleaved_equiv input :
      cipher_interleaved Nr initial_key input =
      inverse_cipher first_key last_key middle_keys input.
    Proof.
      intros. subst inverse_cipher.
      erewrite cipher_interleaved_equiv by eassumption.
      reflexivity.
    Qed.
  End InverseEquivalence.
End Spec.
