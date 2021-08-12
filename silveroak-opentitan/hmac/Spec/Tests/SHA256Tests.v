(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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
Require Import Coq.NArith.NArith.
Require Import HmacSpec.SHA256.
Require Import HmacSpec.Tests.SHA256TestVectors.
Import ListNotations.
Local Open Scope N_scope.

(* Tests for SHA-256 spec *)

(* Uncomment the below for step-by-step tests of intermediate values for test1
   (useful for debugging) *)

(*
(* test Nblocks *)
Goal (let t := test1 in
      Nblocks t.(l) = N.of_nat (List.length (t.(expected_blocks)))).
Proof. vm_compute. reflexivity. Qed.

(* test padded_msg *)
Goal (let t := test1 in
      padded_msg t.(l) t.(msg_N) = t.(expected_padded_msg)).
Proof. vm_compute. reflexivity. Qed.

(* test first 16 blocks of W for round 0 *)
Goal (let t := test1 in
      let i := 0 in
      let expected_W := nth (N.to_nat i) t.(expected_blocks) [] in
      firstn 16 (W t.(l) t.(msg_N) i) = expected_W).
Proof. vm_compute. reflexivity. Qed.

(* test round 0 *)
Goal (let t := test1 in
      let i := 0%nat in
      let old_H := H0 in
      let expected_H := nth i t.(expected_intermediate_digests) [] in
      sha256_step t.(l) t.(msg_N) old_H i = expected_H).
Proof. vm_compute. reflexivity. Qed.
*)

(* test final digest *)
Goal (let t := test1 in
      sha256 t.(l) t.(msg_N) = t.(expected_digest)).
Proof. vm_compute. reflexivity. Qed.

(* Uncomment the below for step-by-step tests of intermediate values for test2
   (useful for debugging) *)

(*
(* test Nblocks *)
Goal (let t := test2 in
      Nblocks t.(l) = N.of_nat (List.length (t.(expected_blocks)))).
Proof. vm_compute. reflexivity. Qed.

(* test padded_msg *)
Goal (let t := test2 in
      padded_msg t.(l) t.(msg_N) = t.(expected_padded_msg)).
Proof. vm_compute. reflexivity. Qed.

(* test first 16 blocks of W for round 0 *)
Goal (let t := test2 in
      let i := 0 in
      let expected_W := nth (N.to_nat i) t.(expected_blocks) [] in
      firstn 16 (W t.(l) t.(msg_N) i) = expected_W).
Proof. vm_compute. reflexivity. Qed.

(* test round 0 *)
Goal (let t := test2 in
      let i := 0%nat in
      let old_H := H0 in
      let expected_H := nth i t.(expected_intermediate_digests) [] in
      sha256_step t.(l) t.(msg_N) old_H i = expected_H).
Proof. vm_compute. reflexivity. Qed.

(* test first 16 blocks of W for round 1 *)
Goal (let t := test2 in
      let i := 1 in
      let expected_W := nth (N.to_nat i) t.(expected_blocks) [] in
      firstn 16 (W t.(l) t.(msg_N) i) = expected_W).
Proof. vm_compute. reflexivity. Qed.

(* test round 1 *)
Goal (let t := test2 in
      let i := 1%nat in
      let old_H := nth (i-1) t.(expected_intermediate_digests) [] in
      let expected_H := nth i t.(expected_intermediate_digests) [] in
      sha256_step t.(l) t.(msg_N) old_H i = expected_H).
Proof. vm_compute. reflexivity. Qed.
*)

(* test final digest *)
Goal (let t := test2 in
      sha256 t.(l) t.(msg_N) = t.(expected_digest)).
Proof. vm_compute. reflexivity. Qed.
