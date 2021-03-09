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

Require Import AesSpec.Sbox.
Require Import Cava.Util.List.

Section Spec.
  Variables bytes_per_word Nb : nat.
  Local Notation word := (list byte) (only parsing).
  Local Notation state := (list word) (only parsing).

  Definition sub_bytes : state -> state :=
    map (map forward_sbox).

  Definition inv_sub_bytes : state -> state :=
    map (map inverse_sbox).

  Section Properties.

    Lemma inverse_sbox_prop (x : byte) : inverse_sbox (forward_sbox x) = x.
    Proof.
      destruct x; reflexivity.
    Qed.

    Theorem inverse_sub_bytes (x : state) :
      inv_sub_bytes (sub_bytes x) = x.
    Proof.
      unfold inv_sub_bytes.
      unfold sub_bytes.
      induction x; [reflexivity|].
      simpl.
      rewrite IHx.
      rewrite map_map.
      rewrite map_id_ext.
      { reflexivity. }
      { intro b.
        destruct b; reflexivity. }
    Qed.

    Theorem sub_bytes_length_outer (x : state) :
      length (sub_bytes x) = length x.
    Proof.
      cbv [sub_bytes]. autorewrite with push_length.
      reflexivity.
    Qed.

    Theorem sub_bytes_length_inner (x : state) n r :
      (forall r, In r x -> length r = n) ->
      In r (sub_bytes x) -> length r = n.
    Proof.
      cbv [sub_bytes]; intros Hx Hin.
      apply in_map_iff in Hin.
      destruct Hin as [? [? ?]]. subst.
      autorewrite with push_length.
      auto.
    Qed.

  End Properties.
End Spec.
Hint Resolve sub_bytes_length_inner sub_bytes_length_outer : length.
