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
Require Import HmacSpec.SHA256.
Import ListNotations.
Local Open Scope N_scope.

(* Specification of HMAC as described by RFC 2104, using SHA-256 as the hash
   function: https://datatracker.ietf.org/doc/html/rfc2104 *)

(* From section 2:

   We assume H to be a cryptographic hash function where data is hashed by
   iterating a basic compression function on blocks of data. We denote by B the
   byte-length of such blocks (B=64 for all the above mentioned examples of hash
   functions), and by L the byte-length of hash outputs (L=16 for MD5, L=20 for
   SHA-1).
 *)
Definition B : nat := 64. (* block size for SHA-256  = 512 bits = 64 bytes *)
Definition L : nat := 32. (* output size for SHA-256 = 256 bits = 32 bytes *)


(* From section 2:

   We define two fixed and different strings ipad and opad as follows (the 'i'
   and 'o' are mnemonics for inner and outer):

   ipad = the byte 0x36 repeated B times
   opad = the byte 0x5C repeated B times.
 *)
Definition ipad := concat_bytes (repeat 0x36 B).
Definition opad := concat_bytes (repeat 0x5C B).

(* From section 2 :

  To compute HMAC over the data `text' we perform

     H(K XOR opad, H(K XOR ipad, text))

  Namely:
    (1) append zeros to the end of K to create a B byte string
        (e.g., if K is of length 20 bytes and B=64, then K will be
         appended with 44 zero bytes 0x00)
    (2) XOR (bitwise exclusive-OR) the B byte string computed in step
        (1) with ipad
    (3) append the stream of data 'text' to the B byte string resulting
        from step (2)
    (4) apply H to the stream generated in step (3)
    (5) XOR (bitwise exclusive-OR) the B byte string computed in
        step (1) with opad
    (6) append the H result from step (4) to the B byte string
        resulting from step (5)
    (7) apply H to the stream generated in step (6) and output
        the result
 *)
Section HMAC_SHA256.
  Context (lK : nat) (* key length in bytes *)
          (ldata : nat) (* data length in bytes *)
          (K : N) (* key *)
          (data : N).

  (* step 1 *)
  Definition padded_key : N := N.shiftl K (N.of_nat ((B - lK) * 8)).

  (* lx = length of x in bytes, ly = length of y in bytes *)
  Definition H (lx ly : nat) (x y : N) :=
    (* concatenate x and y (steps 3 and 6) *)
    let input := N.lor (N.shiftl x (N.of_nat (ly * 8))) y in
    (* call SHA256 (steps 4 and 7) *)
    sha256 (N.of_nat ((lx + ly) * 8)) input.

  Definition hmac_sha256 :=
    (* steps 2-4 *)
    let inner := H B ldata (N.lxor padded_key ipad) data in
    (* steps 5-7 *)
    H B ldata (N.lxor padded_key opad) inner.
End HMAC_SHA256.


(* Test 1 from https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/HMAC_SHA256.pdf *)
Definition data := 0x53616D706C65206D65737361676520666F72206B65796C656E3D626C6F636B6C656E.
Definition K := 0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F303132333435363738393A3B3C3D3E3F.
Definition lK : nat := 64.
Definition ldata : nat := 34.

(* Check key padding *)
Goal (padded_key lK K = K).
Proof. vm_compute. reflexivity. Qed.

(* Check K ^ ipad *)
Goal (N.lxor (padded_key lK K) ipad
     = 0x36373435323330313E3F3C3D3A3B383926272425222320212E2F2C2D2A2B282916171415121310111E1F1C1D1A1B181906070405020300010E0F0C0D0A0B0809).
Proof. vm_compute. reflexivity. Qed.

(* Check concatenation *)
Goal (let lx := B in
      let ly := ldata in
      let x := N.lxor (padded_key lK K) ipad in
      let y := data in
      N.lor (N.shiftl x (N.of_nat (ly * 8))) y
      = 0x36373435323330313E3F3C3D3A3B383926272425222320212E2F2C2D2A2B282916171415121310111E1F1C1D1A1B181906070405020300010E0F0C0D0A0B080953616D706C65206D65737361676520666F72206B65796C656E3D626C6F636B6C656E
     ).
Proof. vm_compute. reflexivity. Qed.

(* Check inner hash result *)
Goal (
    H B ldata (N.lxor (padded_key lK K) ipad) data
    = 0xC0918E14C43562B910DB4B8101CF8812C3DA2783C670BFF34D88B3B88E731716).
Proof. vm_compute. reflexivity. Qed.

(* Check final digest *)
Goal (hmac_sha256 lK ldata K data
      =0x8BB9A1DB9806F20DF7F77B82138C7914dD174D59E13DC4D0169C9057B133E1D62).
Proof. vm_compute. reflexivity. Qed.


(* Test case 1 from RFC 2104: *)
Goal
  (hmac_sha256 16 8 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b 0x4869205468657265
   = 0x9294727a3638bb1c13f48ef8158bfc9d).
Proof. Time vm_compute. reflexivity. Qed.
(* Test case 1 from RFC 4231:
   https://datatracker.ietf.org/doc/html/rfc4231 *)
Goal
  (hmac_sha256 20 8 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b 0x4869205468657265
   = 0xb0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7).
Proof. Time vm_compute. reflexivity. Qed.
