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

Require Import Coq.Lists.List.
Require Import Cava.ListUtils.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Class FieldOperations {T : Type} :=
  { fzero : T;
    fone : T;
    fis_zero : T -> bool;
    fopp : T -> T;
    fadd : T -> T -> T;
    fsub : T -> T -> T;
    fmul : T -> T -> T;
    fdiv : T -> T -> T;
    fmodulo : T -> T -> T
  }.
Global Arguments FieldOperations : clear implicits.

Section Polynomials.
  Context {coeff : Type} {ops : FieldOperations coeff}.
  Local Infix "+" := fadd.
  Local Infix "-" := fsub.
  Local Infix "*" := fmul.
  Local Infix "/" := fdiv.
  Local Infix "mod" := fmodulo.

  (* Little-endian polynomial; x^3 + 3x^2 + 1 = [1; 0; 3; 1] *)
  Definition poly : Type := list coeff.

  Definition zero_poly : poly := [].
  Definition one_poly : poly := [fone].

  (* Pad with zeroes to ensure same length *)
  Definition add_poly (A B : poly) : poly :=
    map2 fadd
         (extend A fzero (length B))
         (extend B fzero (length A)).

  Definition opp_poly p := map fopp p.

  Definition sub_poly (A B : poly) : poly :=
    add_poly A (opp_poly B).

  (* Idea borrowed from fiat-crypto's bignum library (see "associational"
     representation). This form is an unordered list where the index represents
     the position in the polynomial. Multiple terms can have the same index. For
     example, x^3 + 3x^2 + 1 could be, completely equivalently:

     [(0,1); (2,3); (3,1)]
     [(2,3); (3,1); (0,1)]
     [(0,1); (2,2); (2,1); (3,1); (3;0)] *)
  Definition indexed_poly : Type := list (nat * coeff).

  (* Multiply a monomial by a polynomial *)
  Definition mul_term (a : nat * coeff) (B : indexed_poly) : indexed_poly :=
    map (fun b =>
           (* add indices, multiply coefficients: ax^n * bx^m = (a*b)x^(n+m) *)
           ((fst a + fst b)%nat, snd a * snd b)) B.

  (* multiply two polynomials in indexed form *)
  Definition mul_indexed_poly (A B : indexed_poly) : indexed_poly :=
    flat_map (fun a => mul_term a B) A.

  Definition to_indexed_poly (A : poly) := combine (seq 0 (length A)) A.

  (* Prefix with zeroes *)
  Definition indexed_term_to_poly (a : nat * coeff) : poly :=
    repeat fzero (fst a) ++ [snd a].

  (* Note: this implementation could be made more efficient by keeping a
     polynomial accumulator and adding terms to the correct coefficient of the
     accumulator one by one. *)
  (* Convert each *term* of the indexed polynomial into a one-term polynomial,
     and add them together *)
  Definition of_indexed_poly (A : indexed_poly) : poly :=
    fold_left add_poly (map indexed_term_to_poly A) zero_poly.

  Definition mul_poly (A B : poly) : poly :=
    let A := to_indexed_poly A in
    let B := to_indexed_poly B in
    let AB := mul_indexed_poly A B in
    of_indexed_poly AB.

  (* Computes (a / b) where a and b are both indexed terms *)
  Definition div_rem_indexed_term (a b : nat * coeff) : (nat * coeff) * (nat * coeff) :=
    if (fst a <? fst b)%nat
    then
      (* degree of b is higher than degree of a, so quotient is 0 *)
      ((0%nat, fzero), a)
    else
      (* degree of a is higher than degree of b *)
      (* quotient of powers; x^a/x^b = x^(a-b) *)
      let qi := (fst a - fst b)%nat in
      (* remainder of powers; we know b <= a, so
         x^a % x^b = (x^b*x^(a-b)) % x^b = 0 *)
      let ri := 0%nat in
      let q :=  (snd a / snd b) in
      let r := (snd a) mod (snd b) in
      ((qi, q), (ri, r)).

  (* Divides polynomial A by term b; returns quotient and remainder *)
  Fixpoint divide_indexed_poly_by_term (A : indexed_poly) (b : nat * coeff)
    : indexed_poly * indexed_poly :=
    match A with
    | [] => ([], []) (* 0 / b *)
    | a :: A' =>
      (* Compute quotient and remainder for A' / b *)
      let rec := divide_indexed_poly_by_term A' b in
      (* Compute quotient and remainder of a / b and add to result *)
      let qr := div_rem_indexed_term a b in
      (fst qr :: fst rec, snd qr :: snd rec)
    end.

  (* divides A by (B ++ [b]); snoc is because B cannot be nil. n is expected to
     always match length of A. *)
  Fixpoint div_rem_poly' n (A B : poly) (b : coeff) {struct n} : poly * poly :=
    if (n <=? length B)%nat
    then
      (* the degree of our numerator A (n-1) is less than the degree of our
         denominator B (length B), so the numerator is necessarily smaller;
         quotient is 0 and remainder is A *)
      ([], A)
    else
      match n with
      | O => (* numerator is zero, therefore quotient and remainder both 0 *)
        ([], [])
      | S n' =>
        (* get last (highest-degree) coefficient of A *)
        let a := nth n' A fzero in
        (* get the quotient and remainder of a / b as indexed terms *)
        let q_ab := ((n' - length B)%nat, a / b) in (* (a / b) x^(n'-length B) *)
        let r_ab := (n', a mod b) in
        (* multiply B * (a // b) *)
        let Bq := mul_poly (indexed_term_to_poly q_ab) B in
        (* subtract Bq from remaining A (excluding last elt) to get new A *)
        let A' := sub_poly (firstn n' A) Bq in
        (* recursively divide with new A' *)
        let qr_AB := div_rem_poly' n' A' B b in
        (* add quotient and remainder of highest terms to recursive quotient
           and remainder *)
        let q := add_poly (indexed_term_to_poly q_ab) (fst qr_AB) in
        let r := add_poly (indexed_term_to_poly r_ab) (snd qr_AB) in
        (q,r)
      end.

  (* Removes terms with zero coefficients *)
  Definition remove_zeroes (A : indexed_poly) : indexed_poly :=
    filter (fun t => negb (fis_zero (snd t))) A.

  (* Removes zeroes from the most significant end of the polynomial *)
  Definition remove_leading_zeroes (A : poly) :=
    let A := to_indexed_poly A in
    let A := remove_zeroes A in
    of_indexed_poly A.

  (* Classical polynomial long division; produces quotient and remainder. B
     (divisor) cannot be zero. *)
  Definition div_rem_poly (A B : poly) : poly * poly :=
    let B := remove_leading_zeroes B in
    div_rem_poly' (length A) A (removelast B) (last B fzero).

  Definition div_poly (A B : poly) : poly := fst (div_rem_poly A B).
  Definition modulo_poly (A B : poly) : poly := snd (div_rem_poly A B).
End Polynomials.
Global Arguments poly : clear implicits.

Section PolynomialTests.
  Local Instance zops : FieldOperations Z :=
    {| fzero := 0;
       fone := 1;
       fis_zero := Z.eqb 0;
       fopp := Z.opp;
       fadd := Z.add;
       fsub := Z.sub;
       fmul := Z.mul;
       fdiv := Z.div;
       fmodulo := Z.modulo |}.

  (* Converting to and from indexed_poly should give the same result *)
  Goal (of_indexed_poly (to_indexed_poly [1;2;3]) = [1;2;3]).
  Proof. vm_compute. reflexivity. Qed.

  (* (1 + 2x)^2 = 1 + 4x + 4x^2 *)
  Goal (mul_poly [1;2] [1;2] = [1;4;4]).
  Proof. vm_compute. reflexivity. Qed.

  (* (1 + 2x + 3x^2)(1 + 2x + 3x^2)
     1 + 2x + 3x^2 + 2x(1 + 2x + 3x^2) + 3x^2(1 + 2x + 3x^2)
     1 + 2x + 3x^2 + 2x + 4x^2 + 6x^3 + 3x^2 + 6x^3 + 9x^4
     1 + 4x + 10x^2 + 12x^3 + 9x^4 *)
  Goal (mul_poly [1;2;3] [1;2;3] = [1;4;10;12;9]).
  Proof. vm_compute. reflexivity. Qed.

  (* 3x * (1 + 2x) + (1 + 2x + 2x^2) = 1 + 5x + 8x^2 *)
  Goal (add_poly (mul_poly [0;3] [1;2]) [1;2;2] = [1;5;8]).
  Proof. vm_compute. reflexivity. Qed.

  (* Note: this test expects 5 zeroes, but any number is fine *)
  (* (1 + 4x + 10x^2 + 12x^3 + 9x^4) ÷ (1 + 2x + 3x^2)
     = (1 + 2x + 3x^2) (no remainder *)
  Goal (div_rem_poly [1;4;10;12;9] [1;2;3] = ([1;2;3],[0;0;0;0;0])).
  Proof. vm_compute. reflexivity. Qed.

  (* 1 ÷ 3x = 0 (remainder: 1) *)
  Goal (div_rem_poly [1] [0;3] = ([],[1])).
  Proof. vm_compute. reflexivity. Qed.

  Goal (div_rem_poly [1;5] [0;3] = ([1],[1;2])).
  Proof. vm_compute. reflexivity. Qed.

  (* 1 + 5x + 8x^2 ÷ 3x = 1 + 2x (remainder 1 + 2x + 2x^2)*)
  Goal (div_rem_poly [1;5;8] [0;3] = ([1;2],[1;2;2])).
  Proof. vm_compute. reflexivity. Qed.
End PolynomialTests.
