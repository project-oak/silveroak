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

Require Import Coq.NArith.NArith.
Local Open Scope N_scope.

(* Specification of SHA-256 as described by FIPS 180-4:
   https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf  *)

(* Notations for bitwise operations, all left-associative *)
Local Infix "<<" := N.shiftl (at level 32, left associativity, only parsing).
Local Infix ">>" := N.shiftr (at level 32, left associativity, only parsing).
Local Infix "⊕" := N.lxor (at level 32, left associativity, only parsing).

(* Word size for SHA-256 *)
Definition w := 32.

(* Addition of w-bit words *)
Definition add_mod (x y : N) := (x + y) mod (2 ^ w).

(* From section 2.2.2:

   The rotate right (circular right shift) operation, where x is a w-bit word
   and n is an integer with 0 <= n < w, is defined by
       ROTR n x = (x >> n) ∨ (x << w - n).
 *)
Definition ROTR n x := N.lor (x >> n) (x << (w - n)).

(* From section 2.2.2:

   The right shift operation, where x is a w-bit word and n is an integer with
   0 <= n < w, is defined by SHR n x = x >> n. *)
Definition SHR n x := x >> n.

(* Six logical functions from section 4.1.2 *)

(* Equation 4.2: Ch(x,y,z) = (x ^ y) ⊕ (¬ x ^ z) *)
Definition Ch (x y z : N) := (N.land x y) ⊕ (N.land (N.lnot x w) z).

(* Equation 4.3: Maj(x, y,z) = (x ^ y) ⊕ (x ^ z) ⊕ (y ^ z) *)
Definition Maj (x y z : N) := (N.land x y) ⊕ (N.land x z) ⊕ (N.land y z).

(* Equation 4.4: Σ{0,256} (x) = (ROTR 2 x) ⊕ (ROTR 13 x) ⊕ (ROTR 22 x) *)
Definition Sigma0 (x : N) := (ROTR 2 x) ⊕ (ROTR 13 x) ⊕ (ROTR 22 x).

(* Equation 4.5: Σ{1,256} (x) = (ROTR 6 x) ⊕ (ROTR 11 x) ⊕ (ROTR 25 x) *)
Definition Sigma1 (x : N) := (ROTR 6 x) ⊕ (ROTR 11 x) ⊕ (ROTR 25 x).

(* Equation 4.6: σ{0,256} (x) = (ROTR 7 x) ⊕ (ROTR 18 x) ⊕ (SHR 3 x) *)
Definition sigma0 (x : N) := (ROTR 7 x) ⊕ (ROTR 18 x) ⊕ (SHR 3 x).

(* Equation 4.7: σ{1,256} (x) = (ROTR 17 x) ⊕ (ROTR 19 x) ⊕ (SHR 10 x) *)
Definition sigma1 (x : N) := (ROTR 17 x) ⊕ (ROTR 19 x) ⊕ (SHR 10 x).
