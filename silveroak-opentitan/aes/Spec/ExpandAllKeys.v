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

Section Spec.
  Context {key rconst : Type}
          (key_expand : nat -> rconst -> key -> rconst * key).

  Definition all_rcons_and_keys
             (Nr : nat) (* number of rounds *)
             (initial_key : key) (initial_rcon : rconst)
    : list (rconst * key) :=
    fst (fold_left_accumulate
           (fun '(rcon, round_key) i => key_expand i rcon round_key)
           (fun x => x) (List.seq 0 Nr) (initial_rcon, initial_key)).

  Definition all_keys Nr initial_key initial_rcon : list key :=
    List.map snd (all_rcons_and_keys Nr initial_key initial_rcon).

  Section Properties.
    Lemma length_all_rcons_and_keys n r k rk rem :
      all_rcons_and_keys n k r = (rk :: rem)%list ->
      length rem = n.
    Proof.
      cbv [all_rcons_and_keys]. intros.
      lazymatch goal with
      | H : @eq (list _) ?x ?y |- _ =>
        assert (length x = length y) by (rewrite H; reflexivity)
      end.
      autorewrite with push_length in *. lia.
    Qed.

    Lemma length_all_keys n k1 k2 r rem_keys :
      all_keys n k1 r = (k2 :: rem_keys)%list ->
      length rem_keys = n.
    Proof.
      cbv [all_keys all_rcons_and_keys]. intros.
      rewrite @map_fold_left_accumulate in *.
      lazymatch goal with
      | H : @eq (list _) ?x ?y |- _ =>
        assert (length x = length y) by (rewrite H; reflexivity)
      end.
      autorewrite with push_length in *. lia.
    Qed.

    Lemma hd_all_rcons_and_keys n k r rk rem :
      all_rcons_and_keys n k r = (rk :: rem)%list -> n <> 0 ->
      rk = (r, k).
    Proof.
      cbv [all_rcons_and_keys]; intros.
      destruct n; [ congruence | ]. cbn [List.seq] in *.
      autorewrite with push_fold_acc in *.
      match goal with
      | H : (?x :: _ = ?y :: _)%list |- _ => inversion H
      end.
      congruence.
    Qed.

    Lemma hd_all_keys n k1 k2 r rem_keys :
      all_keys n k1 r = (k2 :: rem_keys)%list -> n <> 0 -> k1 = k2.
    Proof.
      cbv [all_keys]. intro Hall; intros.
      map_inversion Hall.
      match goal with H : all_rcons_and_keys _ _ _ = _ |- _ =>
                      apply hd_all_rcons_and_keys in H;
                        [ | assumption ] end.
      subst. reflexivity.
    Qed.

    Lemma nth_all_rcons_and_keys' n k r i :
        nth i (all_rcons_and_keys (i+n) k r) (r,k)
        = nth i (all_rcons_and_keys i k r) (r,k).
    Proof.
      cbv [all_rcons_and_keys].
      induction n; intros; [ rewrite Nat.add_0_r; reflexivity | ].
      rewrite Nat.add_succ_r, seq_S, fold_left_accumulate_snoc.
      rewrite app_nth1 by length_hammer. eauto.
    Qed.

    Lemma nth_all_rcons_and_keys n k r i :
      i <= n ->
      nth i (all_rcons_and_keys n k r) (r,k)
      = nth i (all_rcons_and_keys i k r) (r,k).
    Proof.
      intros. replace n with (i+(n-i)) by Lia.lia.
      apply nth_all_rcons_and_keys'.
    Qed.

    Lemma nth_all_rcons_and_keys_succ n k r i :
      S i <= n ->
      nth (S i) (all_rcons_and_keys n k r) (r,k)
      = key_expand i (fst (nth i (all_rcons_and_keys n k r) (r,k)))
                   (snd (nth i (all_rcons_and_keys n k r) (r,k))).
    Proof.
      intros. rewrite !nth_all_rcons_and_keys with (n:=n) by Lia.lia.
      cbv [all_rcons_and_keys].
      rewrite !nth_fold_left_accumulate_id by (rewrite seq_length; Lia.lia).
      rewrite !firstn_all2 by (rewrite seq_length; Lia.lia).
      rewrite seq_S, Nat.add_0_l, fold_left_app. cbn [fold_left].
      repeat destruct_pair_let. reflexivity.
    Qed.

    Lemma nth_all_rcons_and_keys_all_keys n k r i :
      snd (nth i (all_rcons_and_keys n k r) (r,k))
      = nth i (all_keys n k r) k.
    Proof.
      cbv [all_keys]. rewrite <-map_nth with (f:=snd).
      reflexivity.
    Qed.
  End Properties.
End Spec.
