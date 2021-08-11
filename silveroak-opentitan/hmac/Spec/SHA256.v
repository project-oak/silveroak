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

Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Cava.Util.BitArithmetic.
Import ListNotations BigEndianBytes.
Local Open Scope N_scope.

(* Specification of SHA-256 as described by FIPS 180-4:
   https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf  *)

(* Word size for SHA-256 *)
Definition w := 32.

(* Addition of w-bit words *)
Definition add_mod (x y : N) := (x + y) mod (2 ^ w).

(* Truncating shift-left *)
Definition truncating_shiftl (x n : N) := (N.shiftl x n) mod (2 ^ w).

(* Notations for bitwise operations as defined in section 2.2.2, all
   left-associative *)
Local Infix "<<" := truncating_shiftl (at level 32, left associativity, only parsing) : N_scope.
Local Infix ">>" := N.shiftr (at level 32, left associativity, only parsing) : N_scope.
Local Infix "|" := N.lor (at level 32, left associativity, only parsing) : N_scope.
Local Infix "&" := N.land (at level 32, left associativity, only parsing) : N_scope.
Local Infix "⊕" := N.lxor (at level 32, left associativity, only parsing) : N_scope.
Local Notation "¬ x" := (N.lnot x w) (at level 32, only parsing) : N_scope.

(* All addition henceforth is add_mod *)
Local Infix "+" := add_mod (at level 50, left associativity, only parsing) : N_scope.

(* From section 2.2.2:

   The rotate right (circular right shift) operation, where x is a w-bit word
   and n is an integer with 0 <= n < w, is defined by
       ROTR n x = (x >> n) ∨ (x << w - n).
 *)
Definition ROTR n x := (x >> n) | (x << (w - n)).

(* From section 2.2.2:

   The right shift operation, where x is a w-bit word and n is an integer with
   0 <= n < w, is defined by SHR n x = x >> n. *)
Definition SHR n x := x >> n.

(* Equation 4.2: Ch(x,y,z) = (x ^ y) ⊕ (¬ x ^ z) *)
Definition Ch (x y z : N) := (x & y) ⊕ ((¬ x) & z).

(* Equation 4.3: Maj(x, y,z) = (x ^ y) ⊕ (x ^ z) ⊕ (y ^ z) *)
Definition Maj (x y z : N) := (x & y) ⊕ (x & z) ⊕ (y & z).

(* Equation 4.4: Σ{0,256} (x) = (ROTR 2 x) ⊕ (ROTR 13 x) ⊕ (ROTR 22 x) *)
Definition Sigma0 (x : N) := (ROTR 2 x) ⊕ (ROTR 13 x) ⊕ (ROTR 22 x).

(* Equation 4.5: Σ{1,256} (x) = (ROTR 6 x) ⊕ (ROTR 11 x) ⊕ (ROTR 25 x) *)
Definition Sigma1 (x : N) := (ROTR 6 x) ⊕ (ROTR 11 x) ⊕ (ROTR 25 x).

(* Equation 4.6: σ{0,256} (x) = (ROTR 7 x) ⊕ (ROTR 18 x) ⊕ (SHR 3 x) *)
Definition sigma0 (x : N) := (ROTR 7 x) ⊕ (ROTR 18 x) ⊕ (SHR 3 x).

(* Equation 4.7: σ{1,256} (x) = (ROTR 17 x) ⊕ (ROTR 19 x) ⊕ (SHR 10 x) *)
Definition sigma1 (x : N) := (ROTR 17 x) ⊕ (ROTR 19 x) ⊕ (SHR 10 x).

(* From section 4.2.2:

   SHA-224 and SHA-256 use the same sequence of sixty-four constant 32-bit
   words, K{0,256},K{1,256}, ...K{63,256}. These words represent the first
   thirty-two bits of the fractional parts of the cube roots of the first
   sixty-four prime numbers. In hex, these constant words are (from left to
   right):

   428a2f98 71374491 b5c0fbcf e9b5dba5 3956c25b 59f111f1 923f82a4 ab1c5ed5
   d807aa98 12835b01 243185be 550c7dc3 72be5d74 80deb1fe 9bdc06a7 c19bf174
   e49b69c1 efbe4786 0fc19dc6 240ca1cc 2de92c6f 4a7484aa 5cb0a9dc 76f988da
   983e5152 a831c66d b00327c8 bf597fc7 c6e00bf3 d5a79147 06ca6351 14292967
   27b70a85 2e1b2138 4d2c6dfc 53380d13 650a7354 766a0abb 81c2c92e 92722c85
   a2bfe8a1 a81a664b c24b8b70 c76c51a3 d192e819 d6990624 f40e3585 106aa070
   19a4c116 1e376c08 2748774c 34b0bcb5 391c0cb3 4ed8aa4a 5b9cca4f 682e6ff3
   748f82ee 78a5636f 84c87814 8cc70208 90befffa a4506ceb bef9a3f7 c67178f2
 *)
Definition K : list N :=
  [ 0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
    0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
    0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
    0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
    0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
    0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
    0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
    0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 ].

(* From section 5.3.3:

   For SHA-256, the initial hash value, H(0), shall consist of the following eight
   32-bit words, in hex:

   H0(0) = 6a09e667
   H1(0) = bb67ae85
   H2(0) = 3c6ef372
   H3(0) = a54ff53a
   H4(0) = 510e527f
   H5(0) = 9b05688c
   H6(0) = 1f83d9ab
   H7(0) = 5be0cd19
 *)
Definition H0 : list N :=
  [ 0x6a09e667
    ; 0xbb67ae85
    ; 0x3c6ef372
    ; 0xa54ff53a
    ; 0x510e527f
    ; 0x9b05688c
    ; 0x1f83d9ab
    ; 0x5be0cd19 ].

Section WithMessage.
  Context (msg : list byte).

  (* Message length in bits *)
  Definition l : N := N.of_nat (length msg) * 8.

  (* From section 5.1.1:

     Suppose that the length of the message, M, is l bits. Append the bit “1” to
     the end of the message, followed by k zero bits, where k is the smallest,
     non-negative solution to the equation (l + 1 + k = 448) (mod 512). Then
     append the 64-bit block that is equal to the number l expressed using a
     binary representation.
   *)
  (* N.B. calculation of k is done in Z to avoid subtraction underflow *)
  Definition k := Z.to_N ((448 - (Z.of_N l + 1)) mod 512)%Z.

  (* we know that (k+1) must be positive and a multiple of 8, so 1 << k can
     be expressed as bytes *)
  Definition padding : list byte :=
    x80 :: (repeat x00 (((N.to_nat k+1) / 8) - 1)).

  Definition padded_msg_bytes : list byte := msg ++ padding ++ N_to_bytes 8 l.

  (* Convert to w-bit numbers *)
  Definition padded_msg : list N := bytes_to_Ns (N.to_nat w / 8) padded_msg_bytes.

  (* Number of 512-bit blocks in padded message *)
  Definition Nblocks : N := (N.add (N.add l k) 65) / 512.

  (* From section 5.2.1:

     For SHA-1, SHA-224 and SHA-256, the message and its padding are parsed into
     N 512-bit blocks, M(1), M(2),...M(N). Since the 512 bits of the input block
     may be expressed as sixteen 32- bit words, the first 32 bits of message
     block i are denoted M0(i), M1(i), and so on up to M15(i).
   *)
  Definition M (j i : nat) : N := nth (i*16 + j) padded_msg 0.

  (* From section 6.2.2 (step 1):

     Prepare the message schedule, {W(t)}:
     W(t) = Mt(i) for 0 <= t <= 15
     W(t) = σ{1,256}(W_(t-2)) + W(t-7) + σ{0,256}(W(t-15)) + W(t-16) for 16 <= t <= 63
   *)
  Definition W (i : nat) : list N :=
    fold_left (fun (W : list N) t =>
                 let wt :=
                     if (t <? 16)%nat
                     then M t i
                     else
                       let W_tm2 := nth (t-2) W 0 in
                       let W_tm7 := nth (t-7) W 0 in
                       let W_tm15 := nth (t-15) W 0 in
                       let W_tm16 := nth (t-16) W 0 in
                       (sigma1 W_tm2) + W_tm7 + (sigma0 W_tm15) + W_tm16 in
                 W ++ [wt])
              (seq 0 64) [].

  (* See steps in section 6.2.2. *)
  Definition sha256_step
             (H : list N) (i : nat) : list N :=
    (* step 2 : initialize working variables *)
    let a := nth 0 H 0 in
    let b := nth 1 H 0 in
    let c := nth 2 H 0 in
    let d := nth 3 H 0 in
    let e := nth 4 H 0 in
    let f := nth 5 H 0 in
    let g := nth 6 H 0 in
    let h := nth 7 H 0 in

    (* step 3 : loop *)
    let '(a,b,c,d,e,f,g,h) :=
        fold_left
          (fun '(a,b,c,d,e,f,g,h) t =>
             let Kt := nth t K 0 in
             let Wt := nth t (W i) 0 in
             let T1 := h + (Sigma1 e) + (Ch e f g) + Kt + Wt in
             let T2 := (Sigma0 a) + (Maj a b c) in
             let h := g in
             let g := f in
             let f := e in
             let e := d + T1 in
             let d := c in
             let c := b in
             let b := a in
             let a := T1 + T2 in
             (a,b,c,d,e,f,g,h))
          (seq 0 64)
          (a,b,c,d,e,f,g,h) in

    (* step 4 : get ith intermediate hash value *)
    [ a + (nth 0 H 0)
      ; b + (nth 1 H 0)
      ; c + (nth 2 H 0)
      ; d + (nth 3 H 0)
      ; e + (nth 4 H 0)
      ; f + (nth 5 H 0)
      ; g + (nth 6 H 0)
      ; h + (nth 7 H 0) ].

  (* Concatenate the w-bit words of the hash value to get the full digest *)
  Definition concat_digest (H : list N) :=
    flat_map (N_to_bytes (N.to_nat w / 8)) H.

  (* Full SHA-256 computation: loop of sha256_step *)
  Definition sha256 :=
    let n := N.to_nat Nblocks in
    let H := fold_left sha256_step (seq 0 n) H0 in
    concat_digest H.
End WithMessage.
