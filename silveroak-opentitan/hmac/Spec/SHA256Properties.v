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
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import HmacSpec.SHA256.
Import ListNotations.
Local Open Scope N_scope.

Local Ltac lia' := Zify.zify; Z.to_euclidean_division_equations; lia.
Local Ltac t := cbv [k]; lia'.

(* k is a solution to the equation:
     l + 1 + k = 448 (mod 512) *)
Lemma k_correct l : (l + 1 + k l) mod 512 = 448.
Proof. t. Qed.

(* Prove that k < 512 *)
Lemma k_small l : k l < 512.
Proof. t. Qed.

(* Prove that k is the smallest non-negative solution to the equation *)
Lemma k_smallest l n : (l + 1 + n) mod 512 = 448 -> n >= k l.
Proof. t. Qed.
