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

Require Import Cava.Cava.
Require Import Cava.CavaProperties.
Require Import AesSpec.AES256.
Require Import AesSpec.StateTypeConversions.
Require Import AesImpl.SubBytesCircuit.
Require Import AesImpl.CanrightCircuit.
Require Import AesImpl.Pkg.
Import StateTypeConversions.LittleEndian.

Section Equivalence.

  Lemma canright_equals_lut: forall n x,
    n < 256 ->
    x = bitvec_to_signal (nat_to_bitvec_sized 8 n) ->
    aes_sbox_canright true x = aes_sbox_lut true x.
  Proof.
    intros n x H Heq.
    repeat first [lia |
        destruct n; [rewrite Heq; vm_compute; reflexivity|]].
  Qed.

End Equivalence.
