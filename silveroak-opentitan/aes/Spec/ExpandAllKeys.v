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
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Import ListNotations.

Section Spec.
  Context {key : Type}
          (key_expand : nat -> key -> key).

  Definition all_keys'
             (round_idxs : list nat) (initial_key : key)
    : list key * key :=
    fold_left_accumulate
      (fun round_key i => key_expand i round_key)
      round_idxs initial_key.

  Definition all_keys (Nr : nat) (initial_key : key)
    : list key :=
    fst (all_keys' (List.seq 0 Nr) initial_key).

  Section Properties.
    Hint Unfold all_keys all_keys' : expandall.

    Lemma all_keys'_cons i round_idxs k :
      all_keys' (i :: round_idxs) k = (k :: fst (all_keys' round_idxs (key_expand i k)),
                                      snd (all_keys' round_idxs (key_expand i k))).
    Proof.
      autounfold with expandall.
      rewrite fold_left_accumulate_cons_full.
      reflexivity.
    Qed.

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

    Lemma nth_all_keys_plus n rk d i :
        nth i (all_keys (i+n) rk) d
        = nth i (all_keys i rk) d.
    Proof.
      autounfold with expandall. intros.
      induction n; intros; [ rewrite Nat.add_0_r; reflexivity | ].
      rewrite Nat.add_succ_r, seq_S, fold_left_accumulate_snoc.
      rewrite app_nth1 by length_hammer. eauto.
    Qed.

    Lemma nth_all_keys n rk d i :
      i <= n ->
      nth i (all_keys n rk) d
      = nth i (all_keys i rk) d.
    Proof.
      intros. replace n with (i+(n-i)) by lia.
      apply nth_all_keys_plus.
    Qed.

    Lemma nth_all_keys_succ n rk d i :
      S i <= n ->
      nth (S i) (all_keys n rk) d
      = key_expand i (nth i (all_keys n rk) d).
    Proof.
      intros. rewrite !nth_all_keys with (n:=n) by lia.
      autounfold with expandall.
      rewrite !nth_fold_left_accumulate by (rewrite seq_length; lia).
      rewrite !firstn_all2 by (rewrite seq_length; lia).
      rewrite seq_S, Nat.add_0_l, fold_left_app. cbn [fold_left].
      repeat destruct_pair_let. reflexivity.
    Qed.

    Lemma all_keys'_proper_projection
          {T} (projkey : key -> T)
          (key_expand_proper :
             forall i k1 k2, projkey k1 = projkey k2 ->
                        projkey (key_expand i k1) = projkey (key_expand i k2))
          idxs k1 k2:
      projkey k1 = projkey k2 ->
      map projkey (fst (all_keys' idxs k1))
      = map projkey (fst (all_keys' idxs k2)).
    Proof.
      autounfold with expandall.
      revert k1 k2; induction idxs; intros;
        autorewrite with push_fold_acc; cbn [map];
          [ congruence | ].
      erewrite IHidxs with (k2:=key_expand _ k2)
        by eauto using key_expand_proper.
      congruence.
    Qed.

    Lemma length_all_keys_direct (n : nat) (k : key) :
      length (all_keys n k) = S n.
    Proof. cbv [all_keys all_keys']. length_hammer. Qed.
  End Properties.
End Spec.
Hint Rewrite @length_all_keys_direct using solve [eauto] : push_length.

Section Extensionality.
  Lemma all_keys_ext {key} (key_expand key_expand' : nat -> key -> key) n k :
    (forall i k, i < n -> key_expand i k = key_expand' i k) ->
    all_keys key_expand n k = all_keys key_expand' n k.
  Proof.
    intro Hext. cbv [all_keys all_keys'].
    f_equal. apply fold_left_accumulate_ext_In.
    intros *; intro Hseq. apply in_seq in Hseq.
    apply Hext; lia.
  Qed.
End Extensionality.

Section Inverse.
  Context {key : Type}.

  Lemma all_keys'_inv_eq :
    forall (key_expand inv_key_expand : nat -> key -> key)
      round_idxs initial_key final_key
      (final_key_correct :
         final_key = (snd (all_keys' key_expand round_idxs initial_key)))
      (inv_key_expand_key_expand :
         forall i k, inv_key_expand i (key_expand i k) = k),
      fst (all_keys' inv_key_expand (rev round_idxs) final_key)
      = rev (fst (all_keys' key_expand round_idxs initial_key)).
  Proof.
    cbv [all_keys'].
    induction round_idxs using rev_ind; intros;
      autorewrite with listsimpl; cbn [rev app];
        autorewrite with push_fold_acc.
    { rewrite @fold_left_accumulate_snd in *.
      cbn [fold_left rev app map] in *. congruence. }
    { rewrite !fold_left_accumulate_snoc. cbv zeta.
      autorewrite with listsimpl in *. cbn [rev app] in *.
      rewrite @fold_left_accumulate_snd in *.
      rewrite fold_left_app in final_key_correct.
      cbn [fold_left map] in *. rewrite final_key_correct.
      f_equal; [ ]. eapply IHround_idxs; eauto; [ ].
      rewrite fold_left_accumulate_snd.
      rewrite inv_key_expand_key_expand.
      reflexivity. }
  Qed.

  Lemma all_keys'_rev_seq :
    forall n (kexpand kexpand_rev : nat -> key -> key) (initial_key : key)
      (Hequiv : forall i k, kexpand_rev i k = kexpand (n - S i) k),
      fst (all_keys' kexpand (seq 0 n) initial_key)
      = fst (all_keys' kexpand_rev (rev (seq 0 n)) initial_key).
  Proof.
    cbv [all_keys'].
    induction n; intros; [ reflexivity | ].
    rewrite rev_seq_S, Nat.add_0_l. cbn [seq].
    autorewrite with push_fold_acc.
    rewrite <-seq_shift, fold_left_accumulate_map.
    erewrite IHn by (intros; instantiate_app_by_reflexivity).
    rewrite Hequiv, Nat.sub_diag.
    erewrite fold_left_accumulate_ext_In; [ reflexivity | ].
    intros *. rewrite in_rev, rev_involutive, in_seq.
    intros; cbv beta; rewrite Hequiv.
    f_equal; lia.
  Qed.

  Lemma last_all_keys (key_expand : nat -> key -> key) k :
    forall Nr initial_key,
      last (all_keys key_expand Nr initial_key) k =
      fold_left (fun k i => key_expand i k) (seq 0 Nr) initial_key.
  Proof.
    cbv [all_keys all_keys']; intros.
    rewrite fold_left_accumulate_last.
    reflexivity.
  Qed.

  Lemma all_keys'_map_idxs (key_expand : nat -> key -> key) (f : nat -> nat) idxs k :
    all_keys' key_expand (map f idxs) k = all_keys'
                                            (fun i => key_expand (f i)) idxs k.
  Proof.
    cbv [all_keys']. rewrite fold_left_accumulate_map.
    reflexivity.
  Qed.

  Lemma all_keys_inv_eq (key_expand inv_key_expand : nat -> key -> key) :
    forall Nr initial_key final_key
      (final_key_correct :
         forall k,
           final_key = last (all_keys key_expand Nr initial_key) k)
      (inv_key_expand_key_expand :
         forall i k, inv_key_expand (Nr - S i) (key_expand i k) = k),
      all_keys inv_key_expand Nr final_key =
      rev (all_keys key_expand Nr initial_key).
  Proof.
    intros; cbv [all_keys].
    specialize (final_key_correct initial_key).
    rewrite last_all_keys in final_key_correct.
    erewrite <-all_keys'_inv_eq with (final_key:=final_key)
                                    (inv_key_expand:=
                                       fun i => inv_key_expand (Nr - S i))
      by (eassumption || (cbv [all_keys']; rewrite fold_left_accumulate_snd;
                         apply final_key_correct)).
    apply all_keys'_rev_seq. reflexivity.
  Qed.
End Inverse.
