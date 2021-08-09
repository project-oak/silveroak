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
Require Import HmacSpec.HMAC.
Require Import HmacSpec.Tests.HMACTestVectors.
Import ListNotations.
Local Open Scope N_scope.

(* Uncomment the below for step-by-step tests of intermediate values for test1
   (useful for debugging) *)
(*
(* Check key padding *)
Goal (let t := test1 in
      padded_key t.(lK) t.(K) = t.(expected_padded_key)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ ipad *)
Goal (let t := test1 in
      N.lxor t.(expected_padded_key) ipad = t.(expected_xor_K_ipad)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ opad *)
Goal (let t := test1 in
      N.lxor t.(expected_padded_key) opad = t.(expected_xor_K_opad)).
Proof. vm_compute. reflexivity. Qed.

(* Check inner hash result *)
Goal (let t := test1 in
      H B t.(ldata) t.(expected_xor_K_ipad) t.(data) = t.(expected_inner)).
Proof. vm_compute. reflexivity. Qed.
*)

Goal (let t := test1 in
      hmac_sha256 t.(lK) t.(ldata) t.(K) t.(data) = t.(expected_output)).
Proof. vm_compute. reflexivity. Qed.

(* Uncomment the below for step-by-step tests of intermediate values for test2
   (useful for debugging) *)
(*
(* Check key padding *)
Goal (let t := test2 in
      padded_key t.(lK) t.(K) = t.(expected_padded_key)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ ipad *)
Goal (let t := test2 in
      N.lxor t.(expected_padded_key) ipad = t.(expected_xor_K_ipad)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ opad *)
Goal (let t := test2 in
      N.lxor t.(expected_padded_key) opad = t.(expected_xor_K_opad)).
Proof. vm_compute. reflexivity. Qed.

(* Check inner hash result *)
Goal (let t := test2 in
      H B t.(ldata) t.(expected_xor_K_ipad) t.(data) = t.(expected_inner)).
Proof. vm_compute. reflexivity. Qed.
*)

Goal (let t := test2 in
      hmac_sha256 t.(lK) t.(ldata) t.(K) t.(data) = t.(expected_output)).
Proof. vm_compute. reflexivity. Qed.

(* Uncomment the below for step-by-step tests of intermediate values for test3
   (useful for debugging) *)
(*
(* Check key padding *)
Goal (let t := test3 in
      padded_key t.(lK) t.(K) = t.(expected_padded_key)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ ipad *)
Goal (let t := test3 in
      N.lxor t.(expected_padded_key) ipad = t.(expected_xor_K_ipad)).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ opad *)
Goal (let t := test3 in
      N.lxor t.(expected_padded_key) opad = t.(expected_xor_K_opad)).
Proof. vm_compute. reflexivity. Qed.

(* Check inner hash result *)
Goal (let t := test3 in
      H B t.(ldata) t.(expected_xor_K_ipad) t.(data) = t.(expected_inner)).
Proof. vm_compute. reflexivity. Qed.
 *)

Goal (let t := test3 in
      hmac_sha256 t.(lK) t.(ldata) t.(K) t.(data) = t.(expected_output)).
Proof. vm_compute. reflexivity. Qed.
