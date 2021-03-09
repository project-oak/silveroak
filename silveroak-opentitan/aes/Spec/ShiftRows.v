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

Require Import Coq.Lists.List Coq.Arith.Arith.
Require Import Cava.Util.List.
Require Import Psatz.

Section Spec.
  Context {byte : Type}.
  Local Notation word := (list byte) (only parsing).
  Local Notation state := (list word) (only parsing).

  Definition shift_row_once (w : word) :=
    match w with
    | nil => nil
    | h :: t => t ++ h :: nil
    end.

  Fixpoint shift_row (w : word) (r : nat) :=
    match r with
    | O => w
    | S r' => shift_row (shift_row_once w) r'
    end.

  Definition shift_rows_start (st : state) (n : nat) :=
    map2 shift_row st (List.seq n (length st)).

  Definition shift_rows (st : state) :=
    shift_rows_start st 0.

  Definition inv_shift_row (w : word) (r : nat) :=
    rev (shift_row (rev w) r).

  Definition inv_shift_rows (st : state) :=
    map2 inv_shift_row st (List.seq 0 (length st)).

  Section Properties.
    Lemma shift_row_nil : forall shift,
      shift_row nil shift = nil.
    Proof.
      induction shift; [reflexivity|].
      simpl.
      rewrite IHshift.
      reflexivity.
    Qed.

    Lemma inv_shift_row_hd w h : inv_shift_row (w ++ h :: nil) 1 = h :: w.
    Proof.
      unfold inv_shift_row.
      rewrite rev_app_distr.
      simpl.
      rewrite rev_app_distr.
      simpl.
      rewrite rev_involutive.
      reflexivity.
    Qed.

    Lemma inv_shift_row_O w : inv_shift_row w 0 = w.
    Proof.
      unfold inv_shift_row.
      simpl.
      apply rev_involutive.
    Qed.

    Lemma shift_row_plus x a b : shift_row x (a + b) = shift_row (shift_row x a) b.
      generalize dependent x.
      generalize dependent a.
      induction a; intros.
      { simpl.
        reflexivity. }
      { simpl.
        rewrite IHa.
        reflexivity. }
    Qed.

    Lemma inv_shift_row_plus x a b : inv_shift_row x (a + b) = inv_shift_row (inv_shift_row x a) b.
      unfold inv_shift_row.
      rewrite rev_involutive.
      rewrite shift_row_plus.
      reflexivity.
    Qed.

    Lemma inverse_shift_row_1 a : inv_shift_row (shift_row a 1) 1 = a.
      induction a; [reflexivity|].
      simpl.
      rewrite inv_shift_row_hd.
      reflexivity.
    Qed.

    Lemma inverse_shift_row a n : inv_shift_row (shift_row a n) n = a.
    Proof.
      generalize dependent a.
      induction n; intros.
      { simpl.
        rewrite inv_shift_row_O.
        reflexivity. }
      { replace (S n) with (n+1) by lia.
        rewrite shift_row_plus.
        rewrite Nat.add_comm.
        rewrite inv_shift_row_plus.
        rewrite inverse_shift_row_1.
        apply IHn. }
    Qed.

    Theorem inverse_shift_rows (x : state) : inv_shift_rows (shift_rows x) = x.
    Proof.
      unfold shift_rows.
      unfold inv_shift_rows.
      unfold shift_rows_start.

      rewrite map2_length.
      rewrite seq_length.
      rewrite Min.min_idempotent.

      rewrite map2_map2_r.
      erewrite map2_ext by (intros; rewrite inverse_shift_row; reflexivity).
      refine (map2_id_l _ _ _).
      rewrite seq_length.
      lia.
    Qed.

    Theorem shift_rows_length_outer (x : state) :
      length (shift_rows x) = length x.
    Proof.
      cbv [shift_rows shift_rows_start].
      autorewrite with push_length.
      lia.
    Qed.

    Lemma shift_row_once_length (row : list byte) :
      length (shift_row_once row) = length row.
    Proof.
      cbv [shift_row_once]. destruct row; length_hammer.
    Qed.

    Lemma shift_row_length (row : list byte) n :
      length (shift_row row n) = length row.
    Proof.
      revert row; induction n; intros; [ reflexivity | ].
      cbn [shift_row]. rewrite IHn, shift_row_once_length.
      reflexivity.
    Qed.

    Theorem shift_rows_length_inner (x : state) n :
      (forall r, In r x -> length r = n) ->
      forall r, In r (shift_rows x) -> length r = n.
    Proof.
      cbv [shift_rows shift_rows_start]; intros Hx ? Hin.
      apply in_map2_impl in Hin. destruct Hin as [? [? ?]].
      intuition; subst.
      rewrite shift_row_length. auto.
    Qed.

  End Properties.
End Spec.
Hint Resolve shift_rows_length_inner shift_rows_length_outer : length.

Section BasicTests.
  Import ListNotations.

  (* use nat as the "byte" type so shifting is easy to read *)
  Definition nat_rows := [[0; 1; 2; 3]; [4; 5; 6; 7]; [8; 9; 10; 11]; [12; 13; 14; 15]].
  Definition shifted_nat_rows := [[0; 1; 2; 3]; [5; 6; 7; 4]; [10; 11; 8; 9]; [15; 12; 13; 14]].

  Goal (shift_rows nat_rows = shifted_nat_rows).
  Proof. vm_compute. reflexivity. Qed.

  Goal (inv_shift_rows shifted_nat_rows = nat_rows).
  Proof. vm_compute. reflexivity. Qed.

  Goal (inv_shift_rows (shift_rows nat_rows) = nat_rows).
  Proof. vm_compute. reflexivity. Qed.

  (* and do 3x4 to make sure col/row indices aren't ever switched, which can complicated proofs *)
  Definition nat_rows' := [[0; 1; 2; 3]; [4; 5; 6; 7]; [8; 9; 10; 11]].
  Definition shifted_nat_rows' := [[0; 1; 2; 3]; [5; 6; 7; 4]; [10; 11; 8; 9]].

  Goal (shift_rows nat_rows' = shifted_nat_rows').
  Proof. vm_compute. reflexivity. Qed.

  Goal (inv_shift_rows shifted_nat_rows' = nat_rows').
  Proof. vm_compute. reflexivity. Qed.

  (* and 4x3 as well *)
  Definition nat_rows'' := [[0; 1; 2]; [4; 5; 6]; [8; 9; 10]; [12; 13; 14]].
  Definition shifted_nat_rows'' := [[0; 1; 2]; [5; 6; 4]; [10; 8; 9]; [12; 13; 14]].

  Goal (shift_rows nat_rows'' = shifted_nat_rows'').
  Proof. vm_compute. reflexivity. Qed.

  Goal (inv_shift_rows shifted_nat_rows'' = nat_rows'').
  Proof. vm_compute. reflexivity. Qed.

End BasicTests.
