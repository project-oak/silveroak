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
Require Coq.Vectors.Vector. (* not imported due to name collisions with List *)

Require Import Cava.BitArithmetic.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.
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
    match Byte.of_N (list_bits_to_nat x) with
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
  Definition bit_theory : ring_theory fzero fone fadd fmul fsub fopp eq := BoolTheory.

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

  Definition M := list_bits_to_nat m.

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
           (* it is safe to strip bits over 8; they are guaranteed to be 0 *)
           poly_to_byte (firstn 8 (modulo_poly ab m));
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

  Compute (let b57 : byte := Byte.x57 in
           let b83 : byte := Byte.x83 in
           let xy := mul_poly (byte_to_poly b57) (byte_to_poly b83) in
           modulo_poly xy m).

  Definition BitTheory :
    semi_ring_theory (@fzero _ bitops) (@fone _ bitops) (@fadd _ bitops) (@fmul _ bitops) eq.
  Proof.
    constructor; intros; cbn [fzero fone fadd fmul bitops];
      repeat match goal with x : bool |- _ => destruct x end; reflexivity.
  Qed.

  Require Import Derive.
  Derive modulo_formula4
         SuchThat
         (forall p0 p1 p2 p3 : bool,
             modulo_poly [p0; p1; p2; p3]
                         m = modulo_formula4 p0 p1 p2 p3)
         As modulo_formula4_correct.
  Proof.
    intros; cbv [m]. cbv [modulo_poly div_rem_poly]. cbn [length Nat.sub].
    repeat match goal with
           | |- context [remove_leading_zeroes ?m] =>
             let x := constr:(remove_leading_zeroes m) in
             let y := (eval compute in x) in
             change x with y
           end.
    cbn [removelast last].
    vm_compute.
    reflexivity.
  Qed.
  Print modulo_formula4.

  Derive modulo_formula9
         SuchThat
         (forall p0 p1 p2 p3 p4 p5 p6 p7 p8 : bool,
             modulo_poly [p0; p1; p2; p3; p4; p5; p6; p7; p8]
                         m = modulo_formula9 p0 p1 p2 p3 p4 p5 p6 p7 p8)
         As modulo_formula9_correct.
  Proof.
    intros; cbv [m]. cbv [modulo_poly div_rem_poly]. cbn [length Nat.sub].
    repeat match goal with
           | |- context [remove_leading_zeroes ?m] =>
             let x := constr:(remove_leading_zeroes m) in
             let y := (eval compute in x) in
             change x with y
           end.
    cbn [removelast last].
    cbv - [fdiv fmodulo fadd fone fzero fopp fis_zero fsub].
    reflexivity.
  Qed.

  Lemma if_id (b : bool) : (if b then true else false) = b.
  Proof. destruct b; reflexivity. Qed.
  Lemma if_negb (b : bool) : (if b then false else true) = negb b.
  Proof. destruct b; reflexivity. Qed.
  Lemma if_false_formula (b : bool) : (if b then negb b else b) = false.
  Proof. destruct b; reflexivity. Qed.

  Derive modulo_formula
         SuchThat
         (forall p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : bool,
             modulo_poly [p0; p1; p2; p3; p4; p5; p6; p7; p8; p9; p10; p11; p12; p13; p14]
                         m = modulo_formula p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14)
         As modulo_formula_correct.
  Proof.
    intros; cbv [modulo_poly div_rem_poly]. cbn [length Nat.sub].
    let x := constr:(remove_leading_zeroes m) in
    let y := (eval compute in x) in
    change x with y.
    cbn [removelast last fst snd].
    Time
      lazymatch goal with
      | |- ?lhs = _ => set (LHS:=lhs)
      end;
  vm_compute in LHS; subst LHS;
  rewrite !Tauto.if_same;
  rewrite !if_id, !if_negb, !if_false_formula;
  subst modulo_formula; reflexivity. (* 6.1s *)
    Time Qed. (* 5.55s *)
  Print modulo_formula.

  Lemma bit_add_0_l (x : bool) : fadd false x = x.
  Proof. destruct x; reflexivity. Qed.
(*
  Derive mul_formula
         SuchThat
         (forall p0 p1 p2 p3 p4 p5 p6 p7
            q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : bool,
             mul_poly [p0; p1; p2; p3; p4; p5; p6; p7]
                      [q0; q1; q2; q3; q4; q5; q6; q7; q8; q9; q10; q11; q12; q13; q14]
             = mul_formula q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14)
         As mul_formula_correct.
  Proof.
    intros; cbv - [mul_formula fadd fmul].
    subst mul_formula. reflexivity.
  Qed.*)

  (*
  Lemma byte_mul_poly_modulo_poly p q :
    length q = 15%nat ->
    modulo_poly (mul_poly p (firstn 8 (modulo_poly q m))) m
    = modulo_poly (mul_poly p q) m.
  Proof.
    intros; destruct_lists_by_length.
    rewrite modulo_formula_correct.
    cbv [modulo_formula firstn].
    vm_compute.
  Qed.*)

  Lemma byte_mul_comm (a b : byte) :
    fmul a b = fmul b a.
  Proof.
    cbv [fmul byteops].
    rewrite (mul_poly_comm (rtheory:=BitTheory)).
    reflexivity.
  Qed.

  Lemma byte_mul_1_l (a : byte) : fmul fone a = a.
  Proof. destruct a; vm_compute; reflexivity. Qed.

  Compute (fmul Byte.x57 Byte.x83).
  Compute
    ((list_bits_to_nat
        ((fun a b =>
            let ab := mul_poly (byte_to_poly a) (byte_to_poly b) in
            ab) Byte.x57 Byte.x83)) mod M)%N.

  Lemma poly_to_byte_to_poly p :
    (length p = 8)%nat -> byte_to_poly (poly_to_byte p) = p.
  Proof.
    cbv [poly_to_byte byte_to_poly]; intros.
    destruct_lists_by_length.
    repeat match goal with x : bool |- _ => destruct x end;
      vm_compute; reflexivity.
  Qed.

  Lemma byte_to_poly_length b : length (byte_to_poly b) = 8%nat.
  Proof. cbv [byte_to_poly]; length_hammer. Qed.

  Lemma byte_mul_length a b :
    length a = 8%nat -> length b = 8%nat ->
    length (mul_poly a b) = 15%nat.
  Proof.
    intros; destruct_lists_by_length.
    cbv [mul_poly].
    cbn [to_indexed_poly seq combine length].
    cbv [mul_indexed_poly]. cbn [flat_map].
    cbv [mul_term]. cbn [map fst snd app Nat.add].
    rewrite of_indexed_poly_length.
    reflexivity.
  Qed.

  Lemma byte_mul_distr_l (a b c : byte) :
    fmul (fadd a b) c = fadd (fmul a c) (fmul b c).
  Proof.
    cbv [fmul fadd byteops].
    rewrite poly_to_byte_to_poly with (p:=add_poly _ _)
      by (rewrite add_poly_length, !byte_to_poly_length; Lia.lia).
    rewrite (mul_poly_distr_l (rtheory:=BitTheory)).
    remember (byte_to_poly a) as A.
    remember (byte_to_poly b) as B.
    remember (byte_to_poly c) as C.
    rewrite <-(add_poly_modulo_poly_l (rtheory:=BitTheory))
      by (try (intro x; destruct x); reflexivity).
    rewrite (add_poly_comm (rtheory:=BitTheory) (modulo_poly _ _)).
    rewrite <-(add_poly_modulo_poly_l (rtheory:=BitTheory))
      by (try (intro x; destruct x); reflexivity).
    rewrite (modulo_poly_small (add_poly _ _)).
    (*
    2:{
      rewrite add_poly_length.
      rewrite 
    rewrite (mul_poly_comm (rtheory:=BitTheory)).
    rewrite mul_poly_modulo_poly_l.
    Search mul_poly.*)
  Admitted.

  Lemma byte_mul_assoc (a b c : byte) :
    fmul a (fmul b c) = fmul (fmul a b) c.
  Proof.
    cbv [fmul byteops].
    remember (byte_to_poly a) as A.
    remember (byte_to_poly b) as B.
    remember (byte_to_poly c) as C.
    rewrite (mul_poly_comm (rtheory:=BitTheory)).
  Admitted.

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

Require Import Coq.micromega.Lia.
Require Import Cava.Tactics.

Section Properties.
  Existing Instance byteops.
  (*
  Definition BitTheory :
    semi_ring_theory (@fzero _ bitops) (@fone _ bitops) (@fadd _ bitops) (@fmul _ bitops) eq.
  Proof.
    constructor; intros; cbn [fzero fone fadd fmul bitops];
      repeat match goal with x : bool |- _ => destruct x end; reflexivity.
  Qed.
  Definition ByteTheory : semi_ring_theory fzero fone fadd fmul eq.
  Proof.
    constructor.
    { destruct 0; reflexivity. }
    { intros; cbv [fadd byteops].
      rewrite (add_poly_comm (rtheory:=BitTheory)).
      reflexivity. }
    { intros; cbv [fadd byteops].
      Print byte_to_poly.
      Search byte_to_poly.
      rewrite (add_poly_assoc (rtheory:=BitTheory)).
  Locate ring_theory.
  Print Ring_theory.
  Check ring_morphism.
  Definition ByteTheory : semi_ring_theory fzero fone fadd fmul eq.
  Proof.
    constructor.
    { destruct 0; reflexivity. }
    { intros; cbv [fadd byteops].
      rewrite (add_poly_comm (rtheory:=BitTheory)).
      reflexivity. }
    { intros; cbv [fadd byteops].
      Print byte_to_poly.
      Search byte_to_poly.
      rewrite (add_poly_assoc (rtheory:=BitTheory)).
    PolyTheory.
  Definition poly_eq_dec {coeff} (coeff_eq_dec : forall x y, {x = y} + {x <> y}) :
    forall p q : poly coeff, {p = q} + {p <> q} :=
    list_eq_dec coeff_eq_dec.

  Print semi_morph.
  Existing Instance bitops.
  (*
  Context {rmorph : semi_morph (R:=byte) fzero fone fadd fmul eq
                               (C:=poly bool)
                               zero_poly one_poly add_poly mul_poly
                               (fun x y => if poly_eq_dec Bool.bool_dec x y
                                        then true else false)
                               poly_to_byte}.
  Existing Instance byteops.
  Context {rtheory : semi_ring_theory (R:=byte) fzero fone fadd fmul eq}.*)
  Context {rmorph : semi_morph (R:=poly bool)
                               zero_poly one_poly add_poly mul_poly eq
                               (C:=byte) fzero fone fadd fmul Byte.eqb
                               byte_to_poly}.
  Context {rtheory : semi_ring_theory
                       (R:=poly bool)
                       zero_poly one_poly add_poly mul_poly eq}.
  Add Ring fring : rtheory (morphism rmorph).*)

  Context {rtheory : semi_ring_theory
                       (R:=byte) fzero fone fadd fmul eq}.
  Add Ring bytering : rtheory.

  Local Infix "+" := fadd.
  Local Infix "-" := fsub.
  Local Infix "*" := fmul.

  (* This odd property holds on bytes because add/sub are xors *)
  Lemma bytes_sub_is_add (a b : byte) :
    @fadd _ byteops a b = @fadd _ byteops a b.
  Proof. reflexivity. Qed.

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

  Ltac fequal_list :=
    repeat match goal with
           | |- cons _ _ = cons _ _ => f_equal
           end.
  Ltac fequal_vector :=
    repeat match goal with
           | |- Vector.cons _ _ _ _ = Vector.cons _ _ _ _ => f_equal
           end.

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
End Properties.
