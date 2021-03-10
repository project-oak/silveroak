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

Require Import Coq.Init.Byte.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Cava.Util.Tactics.
Require Coq.Vectors.Vector. (* not imported due to name collisions with List *)

Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.List.
Require Import Cava.Util.Vector.
Require Import AesSpec.Polynomial.
Require Import AesSpec.PolynomialProperties.
Import Vector.VectorNotations.
Import ListNotations.
Local Open Scope list_scope.

Section ByteField.
  (* Representation of bytes as polynomials with boolean coefficients;
     relies on N2Bv being little-endian *)
  Definition byte_to_poly (b : byte) : poly bool :=
    Vector.to_list (N2Bv_sized 8 (Byte.to_N b)).
  Definition poly_to_byte (x : poly bool) : byte :=
    match Byte.of_N (N.of_list_bits x) with
    | Some b => b
    | None => Byte.x00 (* error; should not get here! *)
    end.

  (* Operations in GF(2) *)
  Local Instance bitops : FieldOperations bool :=
    {| fzero := false;
       fone := true;
       fis_zero := negb;
       fopp := fun b => b;
       fadd := xorb;
       fsub := xorb;
       fmul := andb;
       fdiv := fun b1 _ => b1; (* divisor must be 1, otherwise division by 0 *)
       fmodulo := fun b1 b2 => xorb b1 (andb b2 b1); (* b1 mod b2 = b1 - b2 * (b1 / b2) *)
    |}.

  (* FIPS 197: 4.2 Multiplication

     In the polynomial representation, multiplication in GF(2^8) (denoted by •)
     corresponds with the multiplication of polynomials modulo an irreducible
     polynomial of degree 8. A polynomial is irreducible if its only divisors
     are one and itself. For the AES algorithm, this irreducible polynomial is

                             m(x) = x^8 + x^4 + x^3 + x + 1                (4.1)

     or {01}{1b} in hexadecimal notation. *)

  (* Modulus for GF(2^8): m(x) = x^8 + x^4 + x^3 + x + 1 *)
  Definition m : poly bool :=
    [true; true; false; true; true; false; false; false; true].

  (* Operations in GF(2^8) *)
  Local Instance byteops : FieldOperations byte :=
    {| fzero := Byte.x00;
       fone := Byte.x01;
       fis_zero := Byte.eqb x00;
       fopp := fun b => b;
       fadd :=
         fun a b => poly_to_byte (add_poly (byte_to_poly a) (byte_to_poly b));
       fsub :=
         fun a b => poly_to_byte (sub_poly (byte_to_poly a) (byte_to_poly b));
       fmul :=
         fun a b =>
           let ab := mul_poly (byte_to_poly a) (byte_to_poly b) in
           poly_to_byte (modulo_poly ab m);
       fdiv :=
         fun a b => poly_to_byte (div_poly (byte_to_poly a) (byte_to_poly b));
       fmodulo :=
         fun a b => poly_to_byte (modulo_poly (byte_to_poly a) (byte_to_poly b));
    |}.

  (* Test case from FIPS : {57} ∘ {83} = {c1} *)
  Goal (let b57 : byte := Byte.x57 in
        let b83 : byte := Byte.x83 in
        let bc1 : byte := Byte.xc1 in
        fmul b57 b83 = bc1).
  Proof. vm_compute. reflexivity. Qed.
End ByteField.

Section Spec.
  Context (bytes_per_word := 4%nat) {Nb : nat}.
  Local Notation column := (Vector.t byte bytes_per_word).
  Local Notation state := (Vector.t column Nb).
  Local Existing Instance byteops.

  (* Convert columns to and from polynomials with coeffs in GF(2^8) *)
  Definition column_to_poly : column -> poly byte := Vector.to_list.
  Definition poly_to_column (c : poly byte) : column :=
    resize_default fzero _ (Vector.of_list c).

  (* Modulus : x^4 + 1 *)
  Definition modulus := [x01; x00; x00; x00; x01]%list.

  (* Multiplication modulo x^4 + 1 *)
  Definition mulmod (x y : poly byte) : poly byte :=
    modulo_poly (mul_poly x y) modulus.

  (* 5.1.3 MixColumns() Transformation

     The MixColumns() transformation operates on the State column-by-column,
     treating each column as a four-term polynomial as described in
     Sec. 4.3. The columns are considered as polynomials over GF(2^8) and
     multiplied modulo x^4 + 1 with a fixed polynomial a(x), given by

               a(x) = {03}x^3 + {01}x^2 + {01}x + {02} (5.5)


     [...]
     As a result of this multiplication, the four bytes in a column are replaced
     by the following:


               c'0 = ({02} ∙ c0) ⊕ ({03} ∙ c1) ⊕ c2 ⊕ c3
               c'1 = c0 ⊕ ({02} ∙ c1) ⊕ ({03} ∙ c2) ⊕ c3
               c'2 = c0 ⊕ c1 ⊕ ({02} ∙ c2) ⊕ ({03} ∙ c3)
               c'3 = ({03} ∙ c0) ⊕ c1 ⊕ c2 ⊕ ({02} ∙ c3)

     (∙ and ⊕ above are multiplication and addition in GF(2^8), respectively)
   *)

  (* MixColumns on a single column using matrix-based formula *)
  Definition mix_single_column (c : column) : column :=
    let sum := Vector.fold_left fadd fzero in
    let prod := Vector.map2 fmul in
    [ sum (prod [x02; x03; x01; x01]%vector c);
      sum (prod [x01; x02; x03; x01]%vector c);
      sum (prod [x01; x01; x02; x03]%vector c);
      sum (prod [x03; x01; x01; x02]%vector c)
    ]%vector.

  (* Polynomial version (slower but possibly helpful for proofs) :*)
  Definition mix_single_column_poly (c : column) : column :=
    let a : poly byte := [x02;x01;x01;x03] in
    let c := column_to_poly c in
    let ac := mulmod a c in
    poly_to_column ac.

  Definition mix_columns : state -> state := Vector.map mix_single_column.

  (* 5.3.3 InvMixColumns() Transformation

     InvMixColumns() is the inverse of the MixColumns() transformation.
     InvMixColumns() operates on the State column-by-column, treating each
     column as a four- term polynomial as described in Sec. 4.3. The columns are
     considered as polynomials over GF(2^8) and multiplied modulo x^4 + 1 with a
     fixed polynomial a^(-1)(x), given by

              a^(-1)(x) = {0b}x 3 + {0d}x 2 + {09}x + {0e}.                (5.9)

     [...]
     As a result of this multiplication, the four bytes in a column are replaced
     by the following:


               c'0 = ({0e} ∙ c0) ⊕ ({0b} ∙ c1) ⊕ ({0d} ∙ c2) ⊕ ({09} ∙ c3)
               c'1 = ({09} ∙ c0) ⊕ ({0e} ∙ c1) ⊕ ({0b} ∙ c2) ⊕ ({0d} ∙ c3)
               c'2 = ({0d} ∙ c0) ⊕ ({09} ∙ c1) ⊕ ({0e} ∙ c2) ⊕ ({0b} ∙ c3)
               c'3 = ({0b} ∙ c0) ⊕ ({0d} ∙ c1) ⊕ ({09} ∙ c2) ⊕ ({0e} ∙ c3)
 *)

  (* InvMixColumns on a single column using matrix-based formula *)
  Definition inv_mix_single_column (c : column) : column :=
    let sum := Vector.fold_left fadd fzero in
    let prod := Vector.map2 fmul in
    [ sum (prod [x0e; x0b; x0d; x09]%vector c);
      sum (prod [x09; x0e; x0b; x0d]%vector c);
      sum (prod [x0d; x09; x0e; x0b]%vector c);
      sum (prod [x0b; x0d; x09; x0e]%vector c)
    ]%vector.

  Definition inv_mix_columns : state -> state := Vector.map inv_mix_single_column.
End Spec.

Section MixColumnsTests.
  Existing Instance byteops.
  Local Open Scope vector_scope.

  (* Check that mix_single_column with polynomials is the same as with matrices *)
  Goal (let c := [x00; x01; x02; x03] in
        mix_single_column_poly c = mix_single_column c).
  Proof. vm_compute. reflexivity. Qed.

  (* test state :
     0
     1
     2
     3 *)
  Goal (let st := [ [x00; x01; x02; x03] ] in (* column-major form *)
        inv_mix_columns (mix_columns st) = st).
  Proof. vm_compute. reflexivity. Qed.

  (* test state :
     0 4 8  12
     1 5 9  13
     2 6 10 14
     3 7 11 15 *)
  Goal ((* state, in column-major form *)
        let st :=
            [ [x00; x01; x02; x03];
              [x04; x05; x06; x07];
              [x08; x09; x0a; x0b];
              [x0c; x0d; x0e; x0f] ] in
        inv_mix_columns (mix_columns st) = st).
  Proof. vm_compute. reflexivity. Qed.
End MixColumnsTests.

Section ByteFieldProperties.
  Existing Instances bitops byteops.
  Local Infix "*" := fmul.
  Local Infix "+" := fadd.
  Local Infix "-" := fsub.

  (* Declare a full ring because we need subtraction for some goals *)
  Definition bit_theory : ring_theory (R:=bool) fzero fone fadd fmul fsub fopp eq
    := BoolTheory.
  Add Ring bitring : bit_theory.

  (* Declare semi-ring for polynomial proof preconditions *)
  Definition BitTheory : semi_ring_theory (R:=bool) fzero fone fadd fmul eq.
  Proof.
    constructor; intros; cbn [fzero fone fadd fmul bitops];
      repeat match goal with x : bool |- _ => destruct x end; reflexivity.
  Qed.

  Lemma poly_to_byte_to_poly p :
    (length p = 8)%nat -> byte_to_poly (poly_to_byte p) = p.
  Proof.
    cbv [poly_to_byte byte_to_poly]; intros.
    destruct_lists_by_length.
    repeat match goal with x : bool |- _ => destruct x end;
      vm_compute; reflexivity.
  Qed.

  Lemma poly_to_byte_to_poly_strip_zeroes p n :
    length p = 8%nat ->
    byte_to_poly (poly_to_byte (p ++ repeat false n)) = p.
  Proof.
    cbv [poly_to_byte byte_to_poly]; intros.
    rewrite N_of_list_bits_app, N_of_list_bits_zero.
    rewrite N.mul_0_r, N.add_0_r.
    apply poly_to_byte_to_poly; auto.
  Qed.

  Lemma byte_to_poly_length b : length (byte_to_poly b) = 8%nat.
  Proof. cbv [byte_to_poly]; length_hammer. Qed.

  Lemma byte_to_poly_inj b1 b2 : byte_to_poly b1 = byte_to_poly b2 -> b1 = b2.
  Proof.
    cbv [byte_to_poly]. intro Heq.
    apply to_list_inj in Heq.
    assert (forall b, N.size_nat (Byte.to_N b) <= 8%nat)
      by (intro b; destruct b; vm_compute; lia).
    apply N2Bv_sized_eq_iff in Heq; [ | solve [auto] .. ].
    apply Byte.to_of_N_iff in Heq.
    rewrite Byte.of_to_N in Heq.
    congruence.
  Qed.

  (* Extra hints for length_hammer *)
  Hint Rewrite @add_poly_length byte_to_poly_length
       using solve [eauto] : push_length.
  Hint Rewrite @mul_poly_length
       using (try apply BitTheory; try apply length_pos_nonnil; length_hammer)
    : push_length.
  Hint Resolve byte_to_poly_length : length.

  (* Some lemmas to simplify boolean expressions *)
  Lemma if_id (b : bool) : (if b then true else false) = b.
  Proof. destruct b; reflexivity. Qed.
  Lemma if_negb (b : bool) : (if b then false else true) = negb b.
  Proof. destruct b; reflexivity. Qed.
  Lemma if_false_formula (b : bool) : (if b then negb b else b) = false.
  Proof. destruct b; reflexivity. Qed.

  (* Complete formula for multiplication of 8-bit vectors in GF(2^8) *)
  Definition mul8 (p q : list bool) : list bool :=
    let p0 := nth 0 p false in
    let p1 := nth 1 p false in
    let p2 := nth 2 p false in
    let p3 := nth 3 p false in
    let p4 := nth 4 p false in
    let p5 := nth 5 p false in
    let p6 := nth 6 p false in
    let p7 := nth 7 p false in
    let q0 := nth 0 q false in
    let q1 := nth 1 q false in
    let q2 := nth 2 q false in
    let q3 := nth 3 q false in
    let q4 := nth 4 q false in
    let q5 := nth 5 q false in
    let q6 := nth 6 q false in
    let q7 := nth 7 q false in
    [ (p0 * q0);
    (p0 * q1) + (p1 * q0);
    (p0 * q2) + (p1 * q1) + (p2 * q0);
    (p0 * q3) + (p1 * q2) + (p2 * q1) + (p3 * q0);
    (p0 * q4) + (p1 * q3) + (p2 * q2) + (p3 * q1) + (p4 * q0);
    (p0 * q5) + (p1 * q4) + (p2 * q3) + (p3 * q2) + (p4 * q1) + (p5 * q0);
    (p0 * q6) + (p1 * q5) + (p2 * q4) + (p3 * q3) + (p4 * q2) + (p5 * q1) + (p6 * q0);
    (p0 * q7) + (p1 * q6) + (p2 * q5) + (p3 * q4) + (p4 * q3) + (p5 * q2) + (p6 * q1) + (p7 * q0);
    (p1 * q7) + (p2 * q6) + (p3 * q5) + (p4 * q4) + (p5 * q3) + (p6 * q2) + (p7 * q1);
    (p2 * q7) + (p3 * q6) + (p4 * q5) + (p5 * q4) + (p6 * q3) + (p7 * q2);
    (p3 * q7) + (p4 * q6) + (p5 * q5) + (p6 * q4) + (p7 * q3);
    (p4 * q7) + (p5 * q6) + (p6 * q5) + (p7 * q4);
    (p5 * q7) + (p6 * q6) + (p7 * q5);
    (p6 * q7) + (p7 * q6);
    (p7 * q7)
    ].

  Lemma mul8_correct p q :
    length p = 8%nat -> length q = 8%nat ->
    mul_poly (ops:=bitops) p q = mul8 p q.
  Proof.
    intros; destruct_lists_by_length.
    vm_compute. rewrite !if_id, !if_negb.
    reflexivity.
  Qed.

  (* Modular reduction with modulus m and 15-bit input:

    round 1 (a[14]):
    a[6] -= a[14]
    a[7] -= a[14]
    a[9] -= a[14]
    a[10] -= a[14]

    round 2 (a[13]):
    a[5] -= a[13]
    a[6] -= a[13]
    a[8] -= a[13]
    a[9] -= a[13]

    round 3 (a[12]):
    a[4] -= a[12]
    a[5] -= a[12]
    a[7] -= a[12]
    a[8] -= a[12]

    round 4 (a[11]):
    a[3] -= a[11]
    a[4] -= a[11]
    a[6] -= a[11]
    a[7] -= a[11]

    round 5 (a[10]):
    a[2] -= a[10]
    a[3] -= a[10]
    a[5] -= a[10]
    a[6] -= a[10]

    round 6 (a[9]):
    a[1] -= a[9]
    a[2] -= a[9]
    a[4] -= a[9]
    a[5] -= a[9]

    round 7 (a[8]):
    a[0] -= a[8]
    a[1] -= a[8]
    a[3] -= a[8]
    a[4] -= a[8]

    final in terms of initial:

    a'[8]  = a[8]  - a[13] - a[12]
    a'[9]  = a[9]  - a[14] - a[13]
    a'[10] = a[10] - a[14]

    a[0] = a[0] - a'[8]
    a[1] = a[1] - a'[9] - a'[8]
    a[2] = a[2] - a'[10] - a'[9]
    a[3] = a[3] - a[11] - a'[10] - a'[8]
    a[4] = a[4] - a[12] - a[11]  - a'[9]  - a'[8]
    a[5] = a[5] - a[13] - a[12]  - a'[10] - a'[9]
    a[6] = a[6] - a[14] - a[13]  - a[11] - a'[10]
    a[7] = a[7] - a[14] - a[12]  - a[11]

   *)
  Definition modulo15 (p : list bool) : list bool :=
    let p0 := nth 0 p false in
    let p1 := nth 1 p false in
    let p2 := nth 2 p false in
    let p3 := nth 3 p false in
    let p4 := nth 4 p false in
    let p5 := nth 5 p false in
    let p6 := nth 6 p false in
    let p7 := nth 7 p false in
    let p8 := nth 8 p false in
    let p9 := nth 9 p false in
    let p10 := nth 10 p false in
    let p11 := nth 11 p false in
    let p12 := nth 12 p false in
    let p13 := nth 13 p false in
    let p14 := nth 14 p false in
    (* redefine p8, p9, and p10 to their final values *)
    let p8 := p8 - p13 - p12 in
    let p9 := p9 - p14 - p13 in
    let p10 := p10 - p14 in
    [ p0 - p8;
    p1 - p9 - p8;
    p2 - p10 - p9;
    p3 - p11 - p10 - p8;
    p4 - p12 - p11 - p9 - p8;
    p5 - p13 - p12 - p10 - p9;
    p6 - p14 - p13 - p11 - p10;
    p7 - p14 - p12 - p11
    ].

  Lemma modulo15_correct p :
    length p = 15%nat -> byte_to_poly (poly_to_byte (modulo_poly p m)) = modulo15 p.
  Proof.
    intros. set (X:=modulo_poly p m).
    destruct_lists_by_length.
    vm_compute in X. subst X.
    (* simplify boolean expressions *)
    rewrite !Tauto.if_same, !if_id, !if_negb, !if_false_formula.
    (* strip zeroes *)
    match goal with
    | |- byte_to_poly
          (poly_to_byte
             [?x0;?x1;?x2;?x3;?x4;?x5;?x6;?x7;
              false;false;false;false;false;false;false]) = _ =>
      let H := fresh in
      pose proof
           (poly_to_byte_to_poly_strip_zeroes
              [x0;x1;x2;x3;x4;x5;x6;x7] 7) as H;
        cbn [repeat app] in H; rewrite H by reflexivity;
          clear H
    end.
    cbv [modulo15 nth].
    fequal_list; clear;
      repeat match goal with b : bool |- _ => destruct b end;
      vm_compute; reflexivity.
  Qed.

  (* Explicit formula for addition of two 8-bit vectors *)
  Definition add8 (p q : list bool) : list bool :=
    let p0 := nth 0 p false in
    let p1 := nth 1 p false in
    let p2 := nth 2 p false in
    let p3 := nth 3 p false in
    let p4 := nth 4 p false in
    let p5 := nth 5 p false in
    let p6 := nth 6 p false in
    let p7 := nth 7 p false in
    let q0 := nth 0 q false in
    let q1 := nth 1 q false in
    let q2 := nth 2 q false in
    let q3 := nth 3 q false in
    let q4 := nth 4 q false in
    let q5 := nth 5 q false in
    let q6 := nth 6 q false in
    let q7 := nth 7 q false in
    [ p0 + q0;
    p1 + q1;
    p2 + q2;
    p3 + q3;
    p4 + q4;
    p5 + q5;
    p6 + q6;
    p7 + q7
    ].

  Lemma add8_correct p q :
    length p = 8%nat -> length q = 8%nat ->
    add_poly p q = add8 p q.
  Proof. intros; destruct_lists_by_length; reflexivity. Qed.

  Local Ltac generalize_bytes_as_polynomials :=
    repeat lazymatch goal with
           | |- context [byte_to_poly ?b] =>
             pose proof (byte_to_poly_length b);
             generalize dependent (byte_to_poly b);
             intros
           end.

  Lemma byte_mul_assoc (a b c : byte) :
    fmul a (fmul b c) = fmul (fmul a b) c.
  Proof.
    cbv [fmul fadd byteops]. apply byte_to_poly_inj.
    rewrite !modulo15_correct, !mul8_correct by length_hammer.
    generalize_bytes_as_polynomials. destruct_lists_by_length.
    lazy [mul8 nth modulo15].
    (* use ring to prove that each element of the list is equal *)
    fequal_list; clear.
    Time all:ring.
  Qed.

  Lemma byte_mul_distr_l (a b c : byte) :
    fmul (fadd a b) c = fadd (fmul a c) (fmul b c).
  Proof.
    cbv [fmul fadd byteops].
    apply byte_to_poly_inj.
    rewrite !modulo15_correct by length_hammer.
    rewrite !mul8_correct by length_hammer.
    rewrite !add8_correct by length_hammer.
    rewrite !poly_to_byte_to_poly by reflexivity.
    pose proof (byte_to_poly_length a).
    pose proof (byte_to_poly_length b).
    pose proof (byte_to_poly_length c).
    generalize dependent (byte_to_poly a); intros A ?.
    generalize dependent (byte_to_poly b); intros B ?.
    generalize dependent (byte_to_poly c); intros C ?.
    destruct_lists_by_length.
    lazy [mul8 add8 nth modulo15].
    (* use ring to prove that each element of the list is equal *)
    fequal_list; clear; ring.
  Qed.

  Definition ByteTheory : semi_ring_theory (R:=byte) fzero fone fadd fmul eq.
  Proof.
    constructor; cbn [fadd fmul byteops].
    { intro b; destruct b; reflexivity. }
    { intros. f_equal. apply @add_poly_comm, BitTheory. }
    { intros. rewrite !poly_to_byte_to_poly by length_hammer.
      f_equal. apply @add_poly_assoc, BitTheory. }
    { intro b; destruct b; vm_compute; reflexivity. }
    { intro b; destruct b; vm_compute; reflexivity. }
    { intros; do 2 f_equal. apply @mul_poly_comm, BitTheory. }
    { apply byte_mul_assoc. }
    { apply byte_mul_distr_l. }
  Qed.
End ByteFieldProperties.
Hint Rewrite @add_poly_length byte_to_poly_length
     using solve [eauto] : push_length.

Section Properties.
  Existing Instance byteops.
  Add Ring bytering : ByteTheory.
  Local Open Scope poly_scope.

  Definition sum (p : poly byte) : byte := List.fold_left fadd p fzero.
  Definition prod (p q : poly byte) : poly byte := map2 fmul p q.

  (* multiplication modulo x^4-1 for 4-digit polynomials *)
  Definition matrix_mulmod (p q : poly byte) : poly byte :=
    let p0 := nth 0 p fzero in
    let p1 := nth 1 p fzero in
    let p2 := nth 2 p fzero in
    let p3 := nth 3 p fzero in
    let q0 := nth 0 q fzero in
    let q1 := nth 1 q fzero in
    let q2 := nth 2 q fzero in
    let q3 := nth 3 q fzero in
    [ sum (prod [q0;q3;q2;q1] [p0;p1;p2;p3]);
      sum (prod [q1;q0;q3;q2] [p0;p1;p2;p3]);
      sum (prod [q2;q1;q0;q3] [p0;p1;p2;p3]);
      sum (prod [q3;q2;q1;q0] [p0;p1;p2;p3])
    ].

  Hint Unfold matrix_mulmod sum prod nth map2 fold_left : matrix_mulmod.

  Lemma matrix_mulmod_assoc a b c :
    length a = 4%nat -> length b = 4%nat -> length c = 4%nat ->
    matrix_mulmod a (matrix_mulmod b c) = matrix_mulmod (matrix_mulmod a b) c.
  Proof.
    intros; destruct_lists_by_length.
    autounfold with matrix_mulmod.
    fequal_list; ring.
  Qed.

  Lemma matrix_mulmod_1_l p :
    length p = 4%nat ->
    matrix_mulmod [fone;fzero;fzero;fzero] p = p.
  Proof.
    intros; destruct_lists_by_length.
    autounfold with matrix_mulmod.
    fequal_list; ring.
  Qed.

  Lemma matrix_mulmod_distr_l a b c :
    length a = 4%nat -> length b = 4%nat -> length c = 4%nat ->
    matrix_mulmod a (map2 fadd b c)
    = map2 fadd (matrix_mulmod a b) (matrix_mulmod a c).
  Proof.
    intros; destruct_lists_by_length.
    autounfold with matrix_mulmod.
    fequal_list; ring.
  Qed.

  Lemma mix_single_column_is_matrix_mulmod d c :
    mix_single_column c = of_list_sized d 4%nat
                                        (matrix_mulmod [x02;x01;x01;x03]
                                                       (Vector.to_list c)).
  Proof.
    cbv [mix_single_column]. constant_vector_simpl c.
    autorewrite with push_to_list.
    autounfold with matrix_mulmod.
    cbv [of_list_sized Vector.of_list].
    rewrite resize_default_id.
    fequal_vector; ring.
  Qed.

  Lemma inv_mix_single_column_is_matrix_mulmod d c :
    inv_mix_single_column c = of_list_sized d 4%nat
                                            (matrix_mulmod [x0e;x09;x0d;x0b]
                                                           (Vector.to_list c)).
  Proof.
    cbv [inv_mix_single_column]. constant_vector_simpl c.
    autorewrite with push_to_list.
    autounfold with matrix_mulmod.
    cbv [of_list_sized Vector.of_list].
    rewrite resize_default_id.
    fequal_vector; try ring.
  Qed.

  Lemma inverse_mix_single_column c :
    inv_mix_single_column (mix_single_column c) = c.
  Proof.
    rewrite inv_mix_single_column_is_matrix_mulmod with (d:=fzero).
    rewrite mix_single_column_is_matrix_mulmod with (d:=fzero).
    autorewrite with push_to_list.
    rewrite matrix_mulmod_assoc by length_hammer.
    match goal with
    | |- context [matrix_mulmod (cons ?a0 ?a) (cons ?b0 ?b)] =>
      compute_expr (matrix_mulmod (cons a0 a) (cons b0 b))
    end.
    rewrite matrix_mulmod_1_l by length_hammer.
    rewrite of_list_sized_to_list; reflexivity.
  Qed.

  Lemma inverse_mix_columns {Nb} (state : Vector.t (Vector.t byte 4) Nb) :
    inv_mix_columns (mix_columns state) = state.
  Proof.
    cbv [inv_mix_columns mix_columns].
    rewrite Vector.map_map.
    apply map_id_ext.
    apply inverse_mix_single_column.
  Qed.

  (* add in this field is the same as add_round_key *)
  Lemma inv_mix_columns_add_comm
        {Nb} (x y : Vector.t (Vector.t byte 4) Nb) :
    Vector.map2 (Vector.map2 fadd) (inv_mix_columns x) (inv_mix_columns y)
    = inv_mix_columns (Vector.map2 (Vector.map2 fadd) x y).
  Proof.
    cbv [inv_mix_columns]. rewrite map2_map, map_map2.
    apply map2_ext; intros.
    rewrite !inv_mix_single_column_is_matrix_mulmod with (d:=fzero).
    apply to_list_inj. autorewrite with push_to_list.
    rewrite matrix_mulmod_distr_l by length_hammer.
    reflexivity.
  Qed.
End Properties.
