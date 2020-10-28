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
  Context {state key rconst : Type}
          (add_round_key : state -> key -> state)
          (sub_bytes shift_rows mix_columns : state -> state)
          (inv_sub_bytes inv_shift_rows inv_mix_columns : state -> state)
          (inv_mix_columns_key : key -> key)
          (key_expand : nat -> rconst -> key -> rconst * key).

  Definition cipher_round_interleaved
             (rcon : rconst) (round_key : key) (st : state) (i : nat)
    : rconst * key * state :=
    let st := if i =? 0
              then add_round_key st round_key
              else
                let st := sub_bytes st in
                let st := shift_rows st in
                let st := mix_columns st in
                let st := add_round_key st round_key in
                st in
    let rcon_key := key_expand i rcon round_key in
    (rcon_key, st).

  (* AES cipher with interleaved key expansion and conditional split on first round *)
  Definition cipher_interleaved
             (Nr : nat) (* number of rounds *)
             (initial_key : key)
             (initial_rcon : rconst)
             (input : state) : state :=
    let st := input in
    let loop_end_state :=
        fold_left
          (fun (loop_state : rconst * key * state) =>
             let '(rcon, round_key, st) := loop_state in
             cipher_round_interleaved rcon round_key st)
          (List.seq 0 Nr)
          (initial_rcon, initial_key, st) in
    let '(_, last_key, st) := loop_end_state in
    let st := sub_bytes st in
    let st := shift_rows st in
    let st := add_round_key st last_key in
    st.

  Section Equivalence.
    Context (key_alt : Type) (* allow cipher to have a different type for keys *)
            (projkey : key -> key_alt) (* convert to alternative key rep *)
            (Nr : nat) (initial_rcon : rconst) (initial_key : key)
            (first_key : key_alt) (middle_keys : list key_alt) (last_key : key_alt)
            (add_round_key_alt : state -> key_alt -> state)
            (add_round_key_alt_equiv :
               forall st k, add_round_key_alt st (projkey k) = add_round_key st k)
            (all_keys_eq :
               List.map projkey
                        (all_keys key_expand Nr initial_key initial_rcon)
               = first_key :: middle_keys ++ [last_key]).

    Let cipher := cipher state key_alt add_round_key_alt sub_bytes shift_rows mix_columns.

    (* Interleaved cipher is equivalent to original cipher *)
    Lemma cipher_interleaved_equiv input :
      cipher_interleaved Nr initial_key initial_rcon input =
      cipher first_key last_key middle_keys input.
    Proof.
      intros. subst cipher.

      (* get the key *pairs* *)
      pose proof all_keys_eq as Hall_keys.
      map_inversion Hall_keys; subst.
      match goal with H : @eq (list key) _ (_ :: _ ++ [_]) |- _ =>
                      rename H into Hall_keys end.

      cbv [cipher_interleaved cipher_round_interleaved Cipher.cipher].
      (* pick the initial key as the default for nth_default *)
      let x := lazymatch type of Hall_keys with all_keys _ _ ?k _ = _ => k end in
      rewrite fold_left_to_seq with (default:=projkey x).
      pose proof (length_all_keys _ _ _ _ _ _ Hall_keys).
      autorewrite with push_length in *.

      (* Nr cannot be 0 *)
      destruct Nr as [|Nr_m1]; [ lia | ].
      pose proof (hd_all_keys _ _ _ _ _ _ Hall_keys ltac:(lia)).
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
      | H : all_keys ?key_expand ?n ?k ?r = _ |- _ =>
        pose (R:= fun (i : nat) (x : rconst * key * state) (y : state) =>
                    x = (nth (S i)
                             (all_rcons_and_keys key_expand n k r) (r,k), y))
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
        rewrite <-add_round_key_alt_equiv.
        f_equal; [ ].
        rewrite nth_all_rcons_and_keys_all_keys.
        rewrite Hall_keys, app_comm_cons.
        rewrite app_nth2 by length_hammer.
        match goal with |- context [nth ?i _ _] =>
                        replace i with 0 by length_hammer end.
        reflexivity. }

      (* use the fold_left invariant lemma *)
      apply fold_left_preserves_relation_seq with (R0:=R); subst R.
      { (* invariant holds at loop start *)
        cbv beta. rewrite nth_all_rcons_and_keys by lia.
        rewrite add_round_key_alt_equiv.
        reflexivity. }
      { (* invariant holds through loop step *)
        cbv beta; intros; subst. repeat destruct_pair_let.
        rewrite Nat.eqb_compare; cbn [Nat.compare].
        rewrite !nth_all_rcons_and_keys_succ by lia.
        rewrite <-add_round_key_alt_equiv.
        f_equal; [ ]. rewrite map_nth.
        lazymatch goal with
        | H : @eq (list key) ?ls (_ :: (?m ++ [_]))%list
          |- context [@nth key ?i ?mk ?d] =>
          replace (nth i mk d) with (nth (S i) ls d)
            by (rewrite H; apply app_nth1; Lia.lia)
        end.
        rewrite <-nth_all_rcons_and_keys_all_keys.
        rewrite !nth_all_rcons_and_keys_succ by lia.
        reflexivity. }
    Qed.
  End Equivalence.
End Spec.