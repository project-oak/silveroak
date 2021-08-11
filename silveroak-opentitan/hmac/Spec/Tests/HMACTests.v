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
Require Import Cava.Util.BitArithmetic.
Require Import HmacSpec.HMAC.
Require Import HmacSpec.Tests.HMACTestVectors.
Import ListNotations BigEndianBytes.
Local Open Scope N_scope.

(* Uncomment the below for step-by-step tests of intermediate values for test1
   (useful for debugging) *)
(*
(* Check key padding *)
Goal (let t := test1 in
      concat_bytes (padded_key t.(K_bytes)) = t.(expected_padded_key)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ ipad *)
Goal (let t := test1 in
      concat_bytes (XOR (N_to_bytes B t.(expected_padded_key)) ipad)
      = t.(expected_xor_K_ipad)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ opad *)
Goal (let t := test1 in
      concat_bytes (XOR (N_to_bytes B t.(expected_padded_key)) opad)
      = t.(expected_xor_K_opad)).
Proof. vm_compute. reflexivity. Qed.

(* Check inner hash result *)
Goal (let t := test1 in
      concat_bytes (H (N_to_bytes B t.(expected_xor_K_ipad)) (N_to_bytes t.(ldata) t.(data)))
      = t.(expected_inner)).
Proof. vm_compute. reflexivity. Qed.
*)

Goal (let t := test1 in
      concat_bytes (hmac_sha256 t.(K_bytes) t.(data_bytes)) = t.(expected_output)).
Proof. vm_compute. reflexivity. Qed.

(* Uncomment the below for step-by-step tests of intermediate values for test2
   (useful for debugging) *)
(*
(* Check key padding *)
Goal (let t := test2 in
      concat_bytes (padded_key t.(K_bytes)) = t.(expected_padded_key)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ ipad *)
Goal (let t := test2 in
      concat_bytes (XOR (N_to_bytes B t.(expected_padded_key)) ipad)
      = t.(expected_xor_K_ipad)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ opad *)
Goal (let t := test2 in
      concat_bytes (XOR (N_to_bytes B t.(expected_padded_key)) opad)
      = t.(expected_xor_K_opad)).
Proof. vm_compute. reflexivity. Qed.

(* Check inner hash result *)
Goal (let t := test2 in
      concat_bytes (H (N_to_bytes B t.(expected_xor_K_ipad)) (N_to_bytes t.(ldata) t.(data)))
      = t.(expected_inner)).
Proof. vm_compute. reflexivity. Qed.
*)

Goal (let t := test2 in
      concat_bytes (hmac_sha256 t.(K_bytes) t.(data_bytes)) = t.(expected_output)).
Proof. vm_compute. reflexivity. Qed.

(* Uncomment the below for step-by-step tests of intermediate values for test3
   (useful for debugging) *)
(*
(* Check key padding *)
Goal (let t := test3 in
      concat_bytes (padded_key t.(K_bytes)) = t.(expected_padded_key)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ ipad *)
Goal (let t := test3 in
      concat_bytes (XOR (N_to_bytes B t.(expected_padded_key)) ipad)
      = t.(expected_xor_K_ipad)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ opad *)
Goal (let t := test3 in
      concat_bytes (XOR (N_to_bytes B t.(expected_padded_key)) opad)
      = t.(expected_xor_K_opad)).
Proof. vm_compute. reflexivity. Qed.

(* Check inner hash result *)
Goal (let t := test3 in
      concat_bytes (H (N_to_bytes B t.(expected_xor_K_ipad)) (N_to_bytes t.(ldata) t.(data)))
      = t.(expected_inner)).
Proof. vm_compute. reflexivity. Qed.
 *)

Goal (let t := test3 in
      concat_bytes (hmac_sha256 t.(K_bytes) t.(data_bytes)) = t.(expected_output)).
Proof. vm_compute. reflexivity. Qed.
