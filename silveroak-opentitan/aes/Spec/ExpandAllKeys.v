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
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Import ListNotations.

Section Spec.
  Context {key : Type}
          (key_expand : nat -> key -> key).

  Definition all_keys'
             (round_idxs : list nat) (initial_key : key)
    : list key * key :=
    fold_left_accumulate
      (fun round_key i => key_expand i round_key)
      (fun x => x) round_idxs initial_key.

  Definition all_keys (Nr : nat) (initial_key : key)
    : list key :=
    fst (all_keys' (List.seq 0 Nr) initial_key).

  Section Properties.
    Hint Unfold all_keys all_keys' : expandall.

    Lemma all_keys_succ n k d :
      let nlist := all_keys n k in
      all_keys (S n) k = nlist ++ [key_expand n (last nlist d)].
    Proof.
      autounfold with expandall. rewrite seq_S, Nat.add_0_l.
      rewrite fold_left_accumulate_snoc. cbv zeta.
      repeat destruct_pair_let.
      rewrite fold_left_accumulate_last, fold_left_accumulate_snd.
      reflexivity.
    Qed.

    Lemma length_all_keys n k k0 rem :
      all_keys n k = (k0 :: rem)%list ->
      length rem = n.
    Proof.
      autounfold with expandall. intros.
      lazymatch goal with
      | H : @eq (list _) ?x ?y |- _ =>
        assert (length x = length y) by (rewrite H; reflexivity)
      end.
      autorewrite with push_length in *. lia.
    Qed.

    Lemma hd_all_keys n k1 k2 rem_keys :
      all_keys n k1 = (k2 :: rem_keys)%list -> n <> 0 -> k1 = k2.
    Proof.
      autounfold with expandall. intros.
      destruct n; [ congruence | ]. cbn [List.seq] in *.
      autorewrite with push_fold_acc in *.
      match goal with
      | H : (?x :: _ = ?y :: _)%list |- _ => inversion H
      end.
      congruence.
    Qed.

    Lemma nth_all_keys_plus n rk i :
        nth i (all_keys (i+n) rk) rk
        = nth i (all_keys i rk) rk.
    Proof.
      autounfold with expandall. intros.
      induction n; intros; [ rewrite Nat.add_0_r; reflexivity | ].
      rewrite Nat.add_succ_r, seq_S, fold_left_accumulate_snoc.
      rewrite app_nth1 by length_hammer. eauto.
    Qed.

    Lemma nth_all_keys n rk i :
      i <= n ->
      nth i (all_keys n rk) rk
      = nth i (all_keys i rk) rk.
    Proof.
      intros. replace n with (i+(n-i)) by lia.
      apply nth_all_keys_plus.
    Qed.

    Lemma nth_all_keys_succ n rk i :
      S i <= n ->
      nth (S i) (all_keys n rk) rk
      = key_expand i (nth i (all_keys n rk) rk).
    Proof.
      intros. rewrite !nth_all_keys with (n:=n) by lia.
      autounfold with expandall.
      rewrite !nth_fold_left_accumulate_id by (rewrite seq_length; lia).
      rewrite !firstn_all2 by (rewrite seq_length; lia).
      rewrite seq_S, Nat.add_0_l, fold_left_app. cbn [fold_left].
      repeat destruct_pair_let. reflexivity.
    Qed.
  End Properties.
End Spec.
