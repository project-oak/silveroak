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

Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.

Require Import AesSpec.ShiftRows.
Require Import AesSpec.SubBytes.
Require Import AesSpec.Sbox.

Section Spec.
  Section Properties.
    Lemma sub_byte_shift_row_once_comm : forall row,
      shift_row_once (map forward_sbox row) =
      map forward_sbox (shift_row_once row).
    Proof.
      intros.
      destruct row; [reflexivity|].
      simpl.
      rewrite map_app.
      reflexivity.
    Qed.

    Lemma sub_byte_shift_row_comm : forall row shift,
      shift_row (map forward_sbox row) shift =
      map forward_sbox (shift_row row shift).
    Proof.
      intros.
      generalize dependent row.
      induction shift; [reflexivity|].
      intros.
      simpl.
      rewrite <- IHshift.
      rewrite sub_byte_shift_row_once_comm.
      reflexivity.
    Qed.

    Lemma sub_bytes_shift_rows_start_comm : forall st n,
      shift_rows_start (sub_bytes st) n =
      sub_bytes (shift_rows_start st n).
    Proof.
      induction st; [reflexivity|].
      intro n.
      unfold shift_rows_start.
      simpl.
      rewrite sub_byte_shift_row_comm.
      unfold shift_rows_start in IHst.
      rewrite IHst.
      reflexivity.
    Qed.

    Theorem sub_bytes_shift_rows_comm : forall st,
      shift_rows (sub_bytes st) = sub_bytes (shift_rows st).
    Proof.
      intros.
      apply (sub_bytes_shift_rows_start_comm st 0).
    Qed.
  End Properties.
End Spec.
