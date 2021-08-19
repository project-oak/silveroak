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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Expr.
Require Import Cava.Semantics.
Require Import Cava.Types.
Require Import HmacSpec.SHA256.
Require Import HmacSpec.Tests.SHA256TestVectors.
Require Import HmacHardware.Sha256.
Import ListNotations.

(**** Convert to/from circuit signals ****)

(* extra cycles to allow for synchronization *)
Definition extra_cycles : nat := 100.

(* convert test vector data into circuit input signals *)
Definition to_sha256_input (t : sha256_test_vector)
  : list (denote_type (input_of (var:=denote_type) sha256)) :=
  (* input must be divided into into 32-bit words *)
  let l := N.to_nat t.(l) in
  let nwords := l / 32 + (if l mod 32 =? 0 then 0 else 1) in
  (* separate bytes for the final word and bytes for non-final words *)
  let non_final_bytes := firstn ((nwords - 1) * 4) t.(msg_bytes) in
  let final_bytes := skipn ((nwords - 1) * 4) t.(msg_bytes) in
  (* convert bytes to words *)
  let non_final_words := BigEndianBytes.bytes_to_Ns 4 non_final_bytes in
  let final_bytes_padded := final_bytes ++ repeat Byte.x00 (4 - length final_bytes) in
  let final_word := BigEndianBytes.concat_bytes final_bytes_padded in
  let final_length := N.of_nat (length final_bytes) in
  (* create actual input signals *)
  let non_final_input : list (denote_type (input_of sha256)) :=
      (* fifo_data_valid=1, fifo_data, is_final=0, final_length=0, clear=0 *)
      List.map (fun data => (1, (data, (0, (0, (0, tt)))))%N) non_final_words in
  let final_input : denote_type (input_of sha256) :=
      (* fifo_data_valid=1, fifo_data, is_final=1, final_length=final_length,
         clear=0 *)
      (1, (final_word, (1, (final_length, (0, tt)))))%N in
  (* create dummy input for cycles while circuit is computing final digest *)
  let nblocks := length (SHA256.padded_msg t.(msg_bytes)) / (512 / N.to_nat w) in
  let dummy_input : denote_type (input_of sha256) := (0, (0, (0, (0, (0, tt)))))%N in
  (* number of cycles = cycles for padding (16 per block)
                        + cycles for compression (64 per block)
                        + extra_cycles *)
  let ndummy := ((64+16)*nblocks + extra_cycles) - length non_final_input - 1 in
  non_final_input ++ [final_input] ++ repeat dummy_input ndummy.

(* extract test result from circuit output signals *)
Definition from_sha256_output
           (out : list (denote_type (output_of (var:=denote_type) sha256)))
  : N :=
  let '(done, (digest, accept_input)) := last out default in
  BigEndianBytes.concat_bytes (concat_digest digest).

(**** Run test vectors ****)

Goal (let t := test1 in
      from_sha256_output (simulate sha256 (to_sha256_input t)) = t.(expected_digest)).
Proof. vm_compute. reflexivity. Qed.

Goal (let t := test2 in
      from_sha256_output (simulate sha256 (to_sha256_input t)) = t.(expected_digest)).
Proof. vm_compute. reflexivity. Qed.

(* Currently fails to produce a valid output, even when run for >500 cycles!
Goal (let t := test3 in
      from_sha256_output (simulate sha256 (to_sha256_input t)) = t.(expected_digest)).
Proof. vm_compute. reflexivity. Qed.
*)
