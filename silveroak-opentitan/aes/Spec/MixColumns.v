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
Require Import Coq.Vectors.Vector.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Cava.BitArithmetic.
Require Import Cava.VectorUtils.
Require Import Cava.ListUtils.
Import VectorNotations.
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

  (* divides (firstn (S n) A) by (B ++ [b]); snoc is because B cannot be nil *)
  Fixpoint div_rem_poly' (n : nat) (A B : poly) (b : coeff) : poly * poly :=
    let a := nth n A fzero in
    (* extract quotient remainder of a / b *)
    let qr_ab := div_rem_indexed_term (n, a) (length B, b) in
    let q_ab := indexed_term_to_poly (fst qr_ab) in
    (* multiply B * (a // b) so highest-degree term of B is close to a *)
    let Bq := mul_poly (B ++ [b]) q_ab in
    (* subtract Bq from A to get new A *)
    let A' := sub_poly A Bq in
    (* we can now ignore nth term of A and proceed to next term *)
    match n with
    | O => (q_ab, A') (* done; A' is the remainder *)
    | S n' =>
      (* recursively divide with new value of A *)
      let qr_AB := div_rem_poly' n' A' B b in
      (add_poly (fst qr_AB) q_ab, snd qr_AB)
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
    div_rem_poly' (length A-1) A (removelast B) (last B fzero).

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
  Goal (div_rem_poly [1] [0;3] = ([0],[1;0])).
  Proof. vm_compute. reflexivity. Qed.

  Goal (div_rem_poly [1;5] [0;3] = ([1],[1;2])).
  Proof. vm_compute. reflexivity. Qed.

  (* 1 + 5x + 8x^2 ÷ 3x = 1 + 2x (remainder 1 + 2x + 2x^2)*)
  Goal (div_rem_poly [1;5;8] [0;3] = ([1;2],[1;2;2])).
  Proof. vm_compute. reflexivity. Qed.
End PolynomialTests.

(* TODO: move *)
Lemma map2_app {A B C} (f : A -> B -> C) la1 la2 lb1 lb2 :
  length la1 = length lb1 ->
  map2 f (la1 ++ la2) (lb1 ++ lb2) = map2 f la1 lb1 ++ map2 f la2 lb2.
Proof.
  revert la1 la2 lb1 lb2.
  induction la1; destruct lb1; cbn [length]; [ reflexivity | congruence .. | ].
  intros. rewrite <-!app_comm_cons. cbn [map2].
  rewrite <-app_comm_cons, IHla1 by Lia.lia.
  reflexivity.
Qed.

Lemma map2_drop_same {A B} (f : A -> A -> B) la :
  map2 f la la = map (fun a => f a a) la.
Proof.
  induction la; [ reflexivity | ].
  cbn [map2]; rewrite IHla; reflexivity.
Qed.

Lemma map_repeat {A B} (f : A -> B) a n :
  map f (repeat a n) = repeat (f a) n.
Proof.
  induction n; [ reflexivity | ].
  cbn [repeat map]; rewrite IHn; reflexivity.
Qed.

(* TODO: move *)
Lemma flat_map_nil_ext {A B} (l : list A) :
  flat_map (B:=B) (fun a => []) l = [].
Proof.
  induction l; [ reflexivity | ].
  cbn [flat_map]. rewrite IHl; reflexivity.
Qed.

Lemma combine_map_l {A B C} (f : A -> B) la (lc : list C) :
  combine (map f la) lc = map (fun ac => (f (fst ac), snd ac))
                              (combine la lc).
Proof.
  revert lc; induction la; [ reflexivity | ].
  destruct lc; intros; [ reflexivity | ].
  cbn [map combine fst snd]. rewrite IHla.
  reflexivity.
Qed.

Lemma flat_map_map {A B C} (f : A -> B) (g : B -> list C) la :
  flat_map g (map f la) = flat_map (fun a => g (f a)) la.
Proof.
  induction la; [ reflexivity | ].
  cbn [map flat_map]. rewrite IHla.
  reflexivity.
Qed.

Lemma map_flat_map {A B C} (f : A -> list B) (g : B -> C) la :
   map g (flat_map f la) = flat_map (fun a => map g (f a)) la.
Proof.
  induction la; [ reflexivity | ].
  cbn [map flat_map]. rewrite map_app.
  rewrite IHla. reflexivity.
Qed.

Lemma flat_map_nonnil {A B} (f : A -> list B) la :
  la <> [] -> (forall a, f a <> nil) ->
  flat_map f la <> nil.
Proof.
  intros ? Hf.
  destruct la as [|a ?]; intros; [ congruence | ].
  specialize (Hf a).
  cbn [flat_map]. intro Heq.
  apply app_eq_nil in Heq.
  tauto.
Qed.

Lemma length_pos_nonnil {A} (l : list A) :
  (0 < length l)%nat -> l <> nil.
Proof.
  destruct l; autorewrite with push_length; (Lia.lia || congruence).
Qed.

Require Import coqutil.Tactics.Tactics.

Section PolynomialProperties.
  Context {A} {ops : FieldOperations A}.
  Context {rtheory : semi_ring_theory fzero fone fadd fmul eq}.
  Add Ring ringA : rtheory.

  Local Infix "+" := fadd.
  Local Infix "-" := fsub.
  Local Infix "*" := fmul.

  Lemma add_poly_0_l p : add_poly zero_poly p = p.
  Proof.
    cbv [add_poly zero_poly extend].
    autorewrite with push_length listsimpl natsimpl.
    induction p; intros; [ reflexivity | ].
    cbn [length repeat map2]. rewrite IHp.
    f_equal; ring.
  Qed.

  Lemma add_poly_comm p q : add_poly p q = add_poly q p.
  Proof.
    cbv [add_poly]. rewrite map2_swap.
    eapply map2_ext. intros; ring.
  Qed.

  Lemma add_poly_cons p0 q0 (p q : poly A) :
    add_poly (p0 :: p) (q0 :: q) = fadd p0 q0 :: add_poly p q.
  Proof.
    cbv [add_poly]. autorewrite with push_length.
    rewrite !extend_cons_S. reflexivity.
  Qed.

  Lemma add_poly_nil_l (p : poly A) : add_poly [] p = p.
  Proof. apply add_poly_0_l. Qed.

  Lemma add_poly_nil_r (p : poly A) : add_poly p [] = p.
  Proof. rewrite add_poly_comm; apply add_poly_0_l. Qed.

  Lemma add_poly_assoc p q r :
    add_poly p (add_poly q r) = add_poly (add_poly p q) r.
  Proof.
    revert q r; induction p; destruct q,r;
      rewrite ?add_poly_nil_l, ?add_poly_nil_r, ?add_poly_cons;
      try reflexivity; [ ].
    rewrite IHp. f_equal; ring.
  Qed.

  Lemma add_poly_app_zero p1 p2 :
    add_poly p1 (repeat fzero (length p1) ++ p2) = p1 ++ p2.
  Proof.
    revert p2; induction p1; intros.
    { rewrite add_poly_nil_l. reflexivity. }
    { cbn [length repeat]. rewrite <-!app_comm_cons.
      rewrite add_poly_cons, IHp1. f_equal; ring. }
  Qed.

  Lemma mul_poly_1_l p : mul_poly one_poly p = p.
  Proof.
    cbv [mul_poly mul_indexed_poly mul_term one_poly]. cbn.
    autorewrite with listsimpl.
    cbv [to_indexed_poly]. rewrite map_map.
    cbv [indexed_term_to_poly].
    induction p using rev_ind; [ reflexivity | ].
    autorewrite with push_length.
    rewrite Nat.add_1_r.
    autorewrite with pull_snoc natsimpl.
    rewrite combine_append by length_hammer.
    rewrite map_app, fold_left_app.
    cbn [combine map fold_left fst snd] in *.
    rewrite IHp. rewrite add_poly_app_zero.
    repeat (f_equal; try ring).
  Qed.

  Lemma of_indexed_poly_app p1 p2 :
    of_indexed_poly (p1 ++ p2) = add_poly (of_indexed_poly p1) (of_indexed_poly p2).
  Proof.
    cbv [of_indexed_poly].
    revert p2; induction p1; intros.
    { autorewrite with listsimpl. cbn [map fold_left].
      rewrite add_poly_0_l. reflexivity. }
    { rewrite <-app_comm_cons. cbn [map fold_left].
      rewrite !add_poly_0_l.
      rewrite !fold_left_assoc with (start:=indexed_term_to_poly _)
                                    (id:=zero_poly)
        by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_nil_r.
      rewrite IHp1, add_poly_assoc. reflexivity. }
  Qed.

  Lemma mul_poly_0_l p : mul_poly zero_poly p = zero_poly.
  Proof. reflexivity. Qed.

  Lemma add_poly_fzero_l n p :
    add_poly (repeat fzero n) p = p ++ repeat fzero (n - length p).
  Proof.
    revert p; induction n; destruct p; intros; autorewrite with natsimpl listsimpl;
      cbn [repeat]; rewrite ?add_poly_nil_l, ?add_poly_nil_r;
      [ reflexivity .. | ].
    rewrite add_poly_cons. rewrite IHn.
    autorewrite with push_length natsimpl. rewrite <-app_comm_cons.
    f_equal; ring.
  Qed.

  Lemma mul_poly_fzero_l q :
    mul_poly [fzero] q = repeat fzero (length q).
  Proof.
    cbv [mul_poly mul_indexed_poly mul_term to_indexed_poly].
    cbn [map flat_map fst snd app length seq combine].
    autorewrite with listsimpl natsimpl.
    induction q using rev_ind; [ reflexivity | ].
    autorewrite with push_length. rewrite Nat.add_1_r.
    autorewrite with pull_snoc natsimpl.
    rewrite combine_append by length_hammer.
    rewrite map_app, of_indexed_poly_app.
    rewrite IHq.
    cbn [combine of_indexed_poly fold_left map fst snd].
    rewrite add_poly_0_l. autorewrite with natsimpl.
    match goal with
      | |- context [fzero * ?x] =>
        replace (fzero * x) with fzero by ring
    end.
    cbv [indexed_term_to_poly]; cbn [fst snd].
    rewrite <-repeat_cons. rewrite add_poly_fzero_l.
    autorewrite with push_length natsimpl. cbn [repeat].
    autorewrite with listsimpl; reflexivity.
  Qed.

  Lemma add_poly_length p q : length (add_poly p q) = Nat.max (length p) (length q).
  Proof. cbv [add_poly]; length_hammer. Qed.

  Lemma mul_poly_singleton_length p0 q : length (mul_poly [p0] q) = length q.
  Proof.
    cbv [mul_poly]. change (to_indexed_poly [p0]) with [(0%nat, p0)].
    cbv [mul_indexed_poly mul_term]. cbn [flat_map fst snd]. autorewrite with listsimpl.
    cbv [to_indexed_poly of_indexed_poly].
    induction q using rev_ind; intros; [ reflexivity | ].
    autorewrite with push_length. rewrite Nat.add_1_r.
    autorewrite with pull_snoc. rewrite !combine_append by length_hammer.
    rewrite !map_app. rewrite fold_left_app.
    cbn [combine map fst snd fold_left]. autorewrite with natsimpl.
    autorewrite with push_length. rewrite add_poly_length, IHq.
    cbv [indexed_term_to_poly]. autorewrite with push_length. cbn [fst].
    Lia.lia.
  Qed.

  (*
  Lemma mul_poly_cons_l p0 p q :
    mul_poly (p0 :: p) q = add_poly (mul_poly [p0] q) (mul_poly (fzero :: p) q).
  Proof.
    cbv [mul_poly].
    cbv [mul_poly to_indexed_poly mul_indexed_poly mul_term].
    autorewrite with push_length.
    cbn [seq combine flat_map fst snd]. rewrite of_indexed_poly_app.
    autorewrite with listsimpl. f_equal; [ ].
    rewrite of_indexed_poly_app.
    match goal with |- ?x = add_poly ?y ?x =>
                    replace y with (repeat fzero (length q))
    end.
    { rewrite add_poly_fzero_l.
      rewrite (proj2 (Nat.sub_0_le _ _));
        [ cbn [repeat]; autorewrite with listsimpl; reflexivity | ].
      (* length of_indexed_poly is max of indices *)
      (* by induction, max of this flat_map's indices is sum of maxes of args *)
      (* args : length p, length q *)
      admit. }
    { induction q using rev_ind; [ reflexivity | ].
      autorewrite with push_length. rewrite Nat.add_1_r.
      autorewrite with pull_snoc natsimpl. cbv [of_indexed_poly] in *.
      rewrite combine_append, !map_app, fold_left_app by length_hammer.
      cbn [combine map fold_left]. rewrite <-IHq.
      rewrite add_poly_fzero_l. cbv [indexed_term_to_poly]. cbn [fst snd].
      autorewrite with push_length natsimpl. cbn [repeat].
      match goal with
      | |- context [fzero * ?x] =>
        replace (fzero * x) with fzero by ring
      end.
      rewrite repeat_cons. autorewrite with listsimpl.
      reflexivity. }
  Admitted.

  Lemma mul_poly_app_l p1 p2 q :
    mul_poly (p1 ++ p2) q = add_poly (mul_poly p1 q) (mul_poly (repeat fzero (length p1) ++ p2) q).
  Proof.
    revert p2 q; induction p1.
    { intros; autorewrite with listsimpl.
      rewrite mul_poly_0_l, add_poly_0_l. reflexivity. }
    { intros; autorewrite with push_length.
      cbn [repeat]. rewrite <-!app_comm_cons.
      rewrite mul_poly_cons_l with (p:=p1).
      rewrite mul_poly_cons_l with (p:=p1 ++ p2).
  Qed.

  Lemma mul_app p1 p2 q :
    of_indexed_poly
      (flat_map
         (fun a : nat * A =>
            map (fun b : nat * A => ((fst a + fst b)%nat, snd a * snd b))
                (p1 ++ p2))) q)
       = add_poly
           (of_indexed_poly
              (flat_map
                 (fun a : nat * A =>
                    map (fun b : nat * A => ((fst a + fst b)%nat, snd a * snd b))
                        (combine (seq 0 (length p)) p)) q))
           (flat_map*)

  Lemma mul_indexed_poly_cons_l p0 p q :
    of_indexed_poly (mul_indexed_poly (p0 :: p) q)
    = add_poly (of_indexed_poly (mul_term p0 q))
               (of_indexed_poly (mul_indexed_poly p q)).
  Proof.
    cbv [of_indexed_poly mul_indexed_poly].
    cbn [flat_map]. rewrite map_app, fold_left_app.
    rewrite fold_left_assoc with (start:=fold_left _ _ _) (id:=zero_poly)
      by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_nil_r.
    reflexivity.
  Qed.

  Lemma of_indexed_poly_cons p0 p :
    of_indexed_poly (p0 :: p) = add_poly (indexed_term_to_poly p0) (of_indexed_poly p).
  Proof.
    cbv [of_indexed_poly]. cbn [map fold_left]. rewrite add_poly_0_l.
    apply fold_left_assoc;
      auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_nil_r.
  Qed.

  Lemma mul_term_cons t p0 p :
    mul_term t (p0 :: p) = ((fst t + fst p0)%nat, snd t * snd p0) :: mul_term t p.
  Proof. reflexivity. Qed.

  (* This pattern comes up quite a bit in later lemmas *)
  Lemma add_poly_arith_helper a b c d :
    add_poly (add_poly a b) (add_poly c d)
    = add_poly (add_poly a c) (add_poly b d).
  Proof.
    rewrite (add_poly_assoc (add_poly a c) b d).
    rewrite (add_poly_comm (add_poly a c) b).
    rewrite (add_poly_assoc b a c).
    rewrite <-(add_poly_assoc (add_poly b a) c d).
    rewrite (add_poly_comm b a).
    reflexivity.
  Qed.

  Lemma mul_indexed_poly_cons_r p q0 q :
    of_indexed_poly (mul_indexed_poly p (q0 :: q))
    = add_poly (of_indexed_poly (mul_term q0 p))
               (of_indexed_poly (mul_indexed_poly p q)).
  Proof.
    cbv [mul_indexed_poly].
    induction p as [|p0 p]; [ reflexivity | ].
    cbn [flat_map]. rewrite !of_indexed_poly_app, !mul_term_cons.
    rewrite !of_indexed_poly_cons. rewrite IHp.
    (* commutativity for very first terms *)
    rewrite (Nat.add_comm (fst q0) (fst p0)).
    replace (snd q0 * snd p0) with (snd p0 * snd q0) by ring.
    apply add_poly_arith_helper.
  Qed.

  Lemma mul_indexed_poly_cons p0 p q0 q :
    of_indexed_poly (mul_indexed_poly (p0 :: p) (q0 :: q)) =
    add_poly (add_poly (indexed_term_to_poly ((fst p0 + fst q0)%nat, snd p0 * snd q0))
                       (of_indexed_poly (mul_term p0 q)))
             (add_poly (of_indexed_poly (mul_term q0 p))
                       (of_indexed_poly (mul_indexed_poly p q))).
  Proof.
    rewrite !mul_indexed_poly_cons_l. rewrite !mul_term_cons.
    rewrite !mul_indexed_poly_cons_r. rewrite !of_indexed_poly_cons.
    reflexivity.
  Qed.

  Lemma mul_indexed_poly_comm p q :
    of_indexed_poly (mul_indexed_poly p q) = of_indexed_poly (mul_indexed_poly q p).
  Proof.
    revert q; induction p as [|p0 p]; destruct q as [|q0 q]; intros;
      [ cbn [of_indexed_poly mul_indexed_poly mul_term map flat_map app fold_left];
        rewrite ?flat_map_nil_ext; reflexivity .. | ].
    rewrite !mul_indexed_poly_cons.
    (* commutativity for very first terms *)
    rewrite (Nat.add_comm (fst q0) (fst p0)).
    replace (snd q0 * snd p0) with (snd p0 * snd q0) by ring.
    rewrite IHp. apply add_poly_arith_helper.
  Qed.

  Lemma mul_poly_comm p q : mul_poly p q = mul_poly q p.
  Proof.
    cbv [mul_poly]. rewrite mul_indexed_poly_comm. reflexivity.
  Qed.

  Lemma mul_term_mul_indexed_poly_l t p q :
    of_indexed_poly (mul_term t (mul_indexed_poly p q))
    = of_indexed_poly (mul_indexed_poly (mul_term t p) q).
  Proof.
    cbv [of_indexed_poly mul_term mul_indexed_poly].
    revert q; induction p as [|p0 p]; intros; [ reflexivity | ].
    cbn [flat_map map]. rewrite !map_app, !fold_left_app.
    cbn [fst snd].
    rewrite !fold_left_assoc with (start:=fold_left _ _ _)
                                  (id:=zero_poly)
      by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_nil_r.
    rewrite IHp. f_equal; [ ].
    rewrite !map_map. cbn [fst snd].
    f_equal; [ ]. apply map_ext; intros.
    repeat (f_equal; try Lia.lia; try ring).
  Qed.

  Lemma mul_term_mul_indexed_poly_r t p q :
    of_indexed_poly (mul_term t (mul_indexed_poly p q))
    = of_indexed_poly (mul_indexed_poly p (mul_term t q)).
  Proof.
    cbv [of_indexed_poly mul_term mul_indexed_poly].
    revert q; induction p as [|p0 p]; intros; [ reflexivity | ].
    cbn [flat_map map]. rewrite !map_app, !fold_left_app.
    cbn [fst snd].
    rewrite !fold_left_assoc with (start:=fold_left _ _ _)
                                  (id:=zero_poly)
      by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_nil_r.
    rewrite IHp. f_equal; [ ].
    rewrite !map_map. cbn [fst snd].
    f_equal; [ ]. apply map_ext; intros.
    repeat (f_equal; try Lia.lia; try ring).
  Qed.

  Lemma mul_term_shift_l i x p : mul_term (S i, x) p = map (fun t => (S (fst t), snd t))
                                                         (mul_term (i,x) p).
  Proof.
    cbv [mul_term]. rewrite map_map. cbn [fst snd]. reflexivity.
  Qed.

  Lemma mul_term_shift_r t p :
    mul_term t (map (fun t => (S (fst t), snd t)) p)
    = map (fun t => (S (fst t), snd t)) (mul_term t p).
  Proof.
    cbv [mul_term]. rewrite !map_map. cbn [fst snd].
    apply map_ext; intros; f_equal; Lia.lia.
  Qed.

  Lemma cons_fzero_distr_l p q :
    fzero :: add_poly p q = add_poly (fzero :: p) (fzero :: q).
  Proof.
    cbv [add_poly]. autorewrite with push_length.
    rewrite !extend_cons_S. cbn [map2]. f_equal; ring.
  Qed.

  (*
  Lemma shift_distr_l p q :
    of_indexed_poly
      (mul_term (1%nat, fone)
                (mul_indexed_poly (to_indexed_poly (add_poly p q)) r))
    = add_poly (of_indexed_poly (mul_term (1%nat, fone) (to_indexed_poly p)))
               (of_indexed_poly (mul_term (1%nat, fone) (to_indexed_poly q))).
    of_indexed_poly (mul_term (1%nat, fone) (of_indexed_poly (add_poly p q))) = add_poly (fzero :: p) (fzero :: q).
  Proof.
    cbv [add_poly]. autorewrite with push_length.
    rewrite !extend_cons_S. cbn [map2]. f_equal; ring.
  Qed.*)

  (*
  Lemma of_indexed_poly_shift p :
    p <> [] ->
    of_indexed_poly (map (fun t => (S (fst t), snd t)) p) = fzero :: of_indexed_poly p.
  Proof.
    induction p as [|p0 p]; [ congruence | ].
    intros; cbn [map]; rewrite of_indexed_poly_cons.
    destruct p as [|p1 p]; intros.
    { subst. cbv [of_indexed_poly]. cbn [map fold_left].
      rewrite add_poly_0_l.
      cbv [indexed_term_to_poly]. cbn [fst snd].
      rewrite add_poly_nil_r. reflexivity. }
    { set (P:=p1::p) in *.
      rewrite IHp by (subst P; congruence).
      cbv [of_indexed_poly]. cbn [map fold_left].
      cbv [indexed_term_to_poly]. cbn [fst snd].
      cbn [repeat]. rewrite <-app_comm_cons.
      rewrite <-cons_fzero_distr_l.
      rewrite !fold_left_assoc with (start:=add_poly _ _)
                                    (id:=zero_poly)
        by auto using add_poly_0_l, add_poly_comm, add_poly_assoc, add_poly_nil_r.
      rewrite add_poly_0_l.
      reflexivity. }
  Qed.*)

  Lemma to_indexed_poly_cons p0 (p : poly A) :
    to_indexed_poly (p0 :: p) = (0%nat, p0) :: map (fun t => (S (fst t), snd t)) (to_indexed_poly p).
  Proof.
    cbv [to_indexed_poly]. cbn [length seq combine].
    erewrite <-seq_shift. rewrite combine_map_l.
    reflexivity.
  Qed.

  Definition shift_poly (p : poly A) : poly A :=
    match p with
    | [] => []
    | _ => fzero :: p
    end.

  Lemma indexed_term_to_poly_shift_poly n x :
    indexed_term_to_poly (S n, x) = shift_poly (indexed_term_to_poly (n, x)).
  Proof.
    cbv [indexed_term_to_poly shift_poly]. cbn [fst snd repeat].
    destruct n; cbn [repeat]; [ reflexivity | ].
    rewrite <-!app_comm_cons. reflexivity.
  Qed.

  Lemma add_poly_shift_poly p q :
    add_poly (shift_poly p) (shift_poly q) = shift_poly (add_poly p q).
  Proof.
    destruct p, q; cbn [shift_poly];
      rewrite ?add_poly_nil_l, ?add_poly_nil_r; [ reflexivity .. | ].
    rewrite !add_poly_cons. cbn [shift_poly].
    f_equal; ring.
  Qed.

  (*
  Lemma of_indexed_poly_shift_poly p :
    of_indexed_poly (mul_term (1%nat, fone) p) = shift_poly (of_indexed_poly p).
  Proof.
    induction p as [|p0 p]; [ reflexivity | ]. rewrite mul_term_cons. cbn [fst snd].
    rewrite !of_indexed_poly_cons. rewrite IHp.
    rewrite indexed_term_to_poly_shift_poly, add_poly_shift_poly.
    replace (fone * snd p0) with (snd p0) by ring.
    destruct p0; reflexivity.
  Qed.*)

  Lemma of_indexed_poly_shift p :
    of_indexed_poly (map (fun t => (S (fst t), snd t)) p) = shift_poly (of_indexed_poly p).
  Proof.
    induction p as [|p0 p]; cbn [map]; [ reflexivity | ].
    rewrite !of_indexed_poly_cons, IHp.
    rewrite indexed_term_to_poly_shift_poly, add_poly_shift_poly.
    destruct p0; reflexivity.
  Qed.

  Lemma mul_poly_cons_l p0 (p q : poly A) :
    mul_poly (p0 :: p) q = add_poly (of_indexed_poly (mul_term (0%nat, p0) (to_indexed_poly q)))
                                   (shift_poly (mul_poly p q)).
  Proof.
    intros; cbv [mul_poly]. rewrite to_indexed_poly_cons.
    rewrite mul_indexed_poly_cons_l.
    f_equal; [ ]. cbv [mul_indexed_poly].
    rewrite flat_map_map.
    erewrite flat_map_ext by (intros; apply mul_term_shift_l).
    rewrite <-map_flat_map. rewrite of_indexed_poly_shift.
    reflexivity.
  Qed.
  (*

  Lemma mul_poly_cons_l p0 (p q : poly A) :
    p <> nil -> q <> nil ->
    mul_poly (p0 :: p) q = add_poly (of_indexed_poly (mul_term (0%nat, p0) (to_indexed_poly q)))
                                   (fzero :: (mul_poly p q)).
  Proof.
    intros; cbv [mul_poly]. rewrite to_indexed_poly_cons.
    rewrite mul_indexed_poly_cons_l.
    f_equal; [ ]. cbv [mul_indexed_poly].
    rewrite flat_map_map.
    erewrite flat_map_ext by (intros; apply mul_term_shift).
    rewrite <-map_flat_map.
    rewrite of_indexed_poly_shift; [ reflexivity | ].
    cbv [to_indexed_poly mul_term]. destruct p, q; [ congruence .. | ].
    apply flat_map_nonnil; intros; apply length_pos_nonnil; length_hammer.
  Qed.
*)
  Lemma add_poly_snoc n x y :
    add_poly (repeat fzero n ++ [x]) (repeat fzero n ++ [y]) = repeat fzero n ++ [x + y].
  Proof.
    cbv [add_poly]. rewrite !extend_le by length_hammer.
    induction n; [ reflexivity | ].
    cbn [repeat]. rewrite <-!app_comm_cons. cbn [map2].
    rewrite IHn. f_equal; ring.
  Qed.

  Lemma mul_term_distr_l x y p :
    of_indexed_poly (mul_term (0%nat, x + y) p) = add_poly (of_indexed_poly (mul_term (0%nat, x) p))
                                                         (of_indexed_poly (mul_term (0%nat, y) p)).
  Proof.
    cbv [mul_term]. cbn [fst snd].
    induction p as [|p0 p]; [ reflexivity | ].
    cbn [map]. rewrite !of_indexed_poly_cons.
    rewrite IHp. cbv [indexed_term_to_poly]. cbn [fst snd].
    replace ((x + y) * snd p0) with (x * snd p0 + y * snd p0) by ring.
    rewrite <-add_poly_snoc.
    apply add_poly_arith_helper.
  Qed.

  Lemma mul_poly_singleton x (p : poly A) :
    mul_poly [x] p = of_indexed_poly (mul_term (0%nat, x) (to_indexed_poly p)).
  Proof.
    cbv [mul_poly mul_indexed_poly].
    cbn [to_indexed_poly length seq combine map flat_map].
    autorewrite with listsimpl. reflexivity.
  Qed.

  Lemma mul_term_mul_term t1 t2 p :
    mul_term t1 (mul_term t2 p) = mul_term ((fst t1 + fst t2)%nat, snd t1 * snd t2) p.
  Proof.
    cbv [mul_term]. rewrite !map_map; cbn [fst snd].
    apply map_ext; intros; f_equal; Lia.lia || ring.
  Qed.

  Lemma indexed_term_to_poly_add_r i x y :
    indexed_term_to_poly (i, x + y) = add_poly (indexed_term_to_poly (i,x))
                                               (indexed_term_to_poly (i,y)).
  Proof.
    cbv [indexed_term_to_poly add_poly]. cbn [fst snd].
    rewrite !extend_le, map2_app by length_hammer.
    rewrite map2_drop_same, map_repeat by auto.
    cbn [map2]. repeat (f_equal; try ring).
  Qed.

  Lemma mul_term_distr_r t p q :
    of_indexed_poly
      (mul_term t (to_indexed_poly (add_poly p q)))
    = add_poly (of_indexed_poly (mul_term t (to_indexed_poly p)))
               (of_indexed_poly (mul_term t (to_indexed_poly q))).
  Proof.
    revert t q; induction p; destruct q; intros;
      [ rewrite ?add_poly_nil_l, ?add_poly_nil_r; reflexivity .. | ].
    rewrite add_poly_cons, !to_indexed_poly_cons, !mul_term_cons.
    rewrite !of_indexed_poly_cons. cbn [fst snd].
    rewrite !mul_term_shift_r, !of_indexed_poly_shift.
    rewrite IHp. rewrite <-add_poly_shift_poly.
    match goal with
    | |- context [ ?a * (?b + ?c) ] =>
      replace (a * (b + c)) with (a * b + a * c) by ring
    end.
    rewrite indexed_term_to_poly_add_r.
    apply add_poly_arith_helper.
  Qed.

  Lemma mul_indexed_poly_distr_r p q r :
    of_indexed_poly
      (mul_indexed_poly p (to_indexed_poly (add_poly q r))) =
    add_poly
      (of_indexed_poly (mul_indexed_poly p (to_indexed_poly q)))
      (of_indexed_poly (mul_indexed_poly p (to_indexed_poly r))).
  Proof.
    revert q r; induction p as [|p0 p]; intros; [ reflexivity | ].
    rewrite !mul_indexed_poly_cons_l. rewrite IHp.
    rewrite mul_term_distr_r. apply add_poly_arith_helper.
  Qed.
  (*
  Lemma add_poly_shift_r t p q :
    add_poly p (of_indexed_poly (mul_term t q)) = add_poly 
(add_poly (of_indexed_poly (mul_term (0%nat, r0) (to_indexed_poly p)))
       (of_indexed_poly (mul_term (1%nat, fone) (mul_indexed_poly (to_indexed_poly r) (to_indexed_poly p)))))*)
  Lemma mul_poly_distr_l p q r :
    mul_poly (add_poly p q) r = add_poly (mul_poly p r) (mul_poly q r).
  Proof.
    rewrite !(mul_poly_comm _ r).
    revert p q; induction r as [|r0 r]; intros;
      [ rewrite !mul_poly_0_l; reflexivity .. | ].
    rewrite !mul_poly_cons_l.
    rewrite mul_term_distr_r. rewrite IHr.
    rewrite <-add_poly_shift_poly.
    apply add_poly_arith_helper.
  Qed.

  Lemma shift_poly_length p : (length p <= length (shift_poly p))%nat.
  Proof. destruct p; cbn [shift_poly]; length_hammer. Qed.

  Lemma mul_poly_shift_l p q :
    mul_poly (shift_poly p) q = shift_poly (mul_poly p q).
  Proof.
    destruct p; [ reflexivity | ].
    cbn [shift_poly]. rewrite !mul_poly_cons_l.
    rewrite <-!mul_poly_singleton.
    rewrite mul_poly_fzero_l, add_poly_fzero_l.
    rewrite (proj2 (Nat.sub_0_le _ _));
      [ cbn [repeat]; autorewrite with listsimpl; reflexivity | ].
    rewrite <-!add_poly_shift_poly.
    rewrite add_poly_length.
    match goal with |- context [length (shift_poly (mul_poly [?x] ?p))] =>
                    pose proof (shift_poly_length (mul_poly [x] p))
    end.
    rewrite !mul_poly_singleton_length in *.
    Lia.lia.
  Qed.

  Lemma mul_term_fzero_r x n :
    mul_term x (to_indexed_poly (repeat fzero n)) = to_indexed_poly (repeat fzero n).
  Admitted.

  Lemma of_indexed_poly_to_indexed_poly p :
    of_indexed_poly (to_indexed_poly p) = p.
  Proof.
    induction p; [ reflexivity | ].
    rewrite !to_indexed_poly_cons, of_indexed_poly_cons.
    rewrite of_indexed_poly_shift. rewrite IHp.
    cbn [indexed_term_to_poly fst snd repeat app].
    destruct p; [ cbn; f_equal; ring | ].
    cbn [shift_poly].
    rewrite add_poly_cons, add_poly_nil_l.
    f_equal; ring.
  Qed.

  Lemma mul_term_to_indexed_poly_of_indexed_poly x p :
    of_indexed_poly (mul_term x (to_indexed_poly (of_indexed_poly p)))
    = of_indexed_poly (mul_term x p).
  Proof.
    induction p as [|p0 p]; intros; [ reflexivity | ].
    rewrite mul_term_cons, !of_indexed_poly_cons.
    rewrite mul_term_distr_r. rewrite IHp. f_equal; [ ].
    cbv [mul_term indexed_term_to_poly to_indexed_poly].
    cbn [fst snd]. autorewrite with push_length.
    rewrite Nat.add_1_r. autorewrite with pull_snoc.
    rewrite combine_append by length_hammer.
    rewrite map_app. cbn [map combine fst snd].
    rewrite of_indexed_poly_app.
    replace (map (fun b : nat * A => ((fst x + fst b)%nat, snd x * snd b))
                 (combine (seq 0 (fst p0)) (repeat fzero (fst p0))))
      with (mul_term x (to_indexed_poly (repeat fzero (fst p0))))
      by (cbv [mul_term to_indexed_poly]; autorewrite with push_length;
          reflexivity).
    rewrite mul_term_fzero_r.
    rewrite of_indexed_poly_to_indexed_poly.
    cbn [of_indexed_poly fold_left map fst snd].
    rewrite add_poly_0_l, add_poly_fzero_l.
    cbv [indexed_term_to_poly]. cbn [fst snd].
    autorewrite with push_length natsimpl.
    cbn [repeat]; autorewrite with listsimpl.
    reflexivity.
  Qed.

  Lemma add_poly_indexed_term_to_poly_fzero_l i p :
    add_poly (indexed_term_to_poly (i, fzero)) p = p ++ repeat fzero (i - length p).
  Admitted.

  Lemma mul_term_shift_poly x p :
    of_indexed_poly (mul_term x (to_indexed_poly (shift_poly p)))
    = shift_poly (of_indexed_poly (mul_term x (to_indexed_poly p))).
  Proof.
    destruct p as [|p0 p]; [ reflexivity | ]. cbn [shift_poly].
    rewrite !to_indexed_poly_cons. cbn [map].
    rewrite !mul_term_cons. cbn [fst snd].
    rewrite !of_indexed_poly_cons.
    rewrite <-add_poly_shift_poly.
    rewrite !mul_term_shift_r, of_indexed_poly_shift.
    rewrite add_poly_assoc. f_equal; [ ].
    rewrite Nat.add_1_r.
    rewrite indexed_term_to_poly_shift_poly.
    replace (snd x * fzero) with fzero by ring.
    rewrite add_poly_indexed_term_to_poly_fzero_l.
    autorewrite with natsimpl.
    rewrite (proj2 (Nat.sub_0_le _ _));
      [ cbn [repeat]; autorewrite with listsimpl; reflexivity | ].
    cbv [indexed_term_to_poly]. cbn [fst snd].
    match goal with
    | |- context [length (shift_poly ?p)] =>
      pose proof (shift_poly_length p)
    end.
    autorewrite with push_length in *. Lia.lia.
  Qed.

  Lemma mul_poly_indexed_term_to_poly t p :
    mul_poly (indexed_term_to_poly t) p = of_indexed_poly (mul_term t (to_indexed_poly p)).
  Proof.
    cbv [indexed_term_to_poly]. destruct t as [i x]. cbn [fst snd].
    revert x p; induction i; intros; cbn [repeat app];
      [ solve [apply mul_poly_singleton] | ].
    rewrite mul_term_shift_l, of_indexed_poly_shift.
    rewrite <-IHi, <-mul_poly_shift_l.
    cbv [shift_poly]. destruct i; reflexivity.
  Qed.

  Lemma mul_term_mul_poly_assoc x p q :
    of_indexed_poly (mul_term x (to_indexed_poly (mul_poly p q)))
    = mul_poly (of_indexed_poly (mul_term x (to_indexed_poly p))) q.
  Proof.
    revert q; induction p as [|p0 p]; intros; [ reflexivity | ].
    rewrite !mul_poly_cons_l. rewrite mul_term_distr_r.
    rewrite to_indexed_poly_cons, mul_term_cons.
    cbn [fst snd]. rewrite of_indexed_poly_cons.
    rewrite mul_term_to_indexed_poly_of_indexed_poly.
    rewrite mul_term_mul_term. cbn [fst snd].
    rewrite mul_poly_distr_l, mul_poly_indexed_term_to_poly.
    f_equal; [ ].
    rewrite mul_term_shift_r.
    rewrite of_indexed_poly_shift.
    rewrite mul_poly_shift_l.
    rewrite <-IHp.
    rewrite mul_term_shift_poly.
    reflexivity.
  Qed.

  Lemma mul_poly_assoc p q r : mul_poly p (mul_poly q r) = mul_poly (mul_poly p q) r.
  Proof.
    revert q r; induction p; intros; [ reflexivity | ].
    rewrite !mul_poly_cons_l. rewrite IHp.
    rewrite mul_poly_distr_l. rewrite mul_term_mul_poly_assoc.
    rewrite mul_poly_shift_l.
    reflexivity.
  Qed.

  Definition PolyTheory
    : semi_ring_theory zero_poly one_poly add_poly mul_poly eq.
  Proof.
    constructor.
    { apply add_poly_0_l. }
    { apply add_poly_comm. }
    { apply add_poly_assoc. }
    { apply mul_poly_1_l. }
    { apply mul_poly_0_l. }
    { apply mul_poly_comm. }
    { apply mul_poly_assoc. }
    { apply mul_poly_distr_l. }
  Qed.

  Print Assumptions PolyTheory.
End PolynomialProperties.

Section ByteField.
  (* Representation of bytes as polynomials with boolean coefficients;
     relies on N2Bv being little-endian *)
  Definition byte_to_poly (b : byte) : poly bool :=
    to_list (N2Bv_sized 8 (Byte.to_N b)).
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
  (*
  Definition byte_theory : ring_theory fzero fone fadd fmul fsub fopp eq.
  Proof.
    constructor.
    { destruct x; reflexivity. }
    { destruct x,y; reflexivity.
  Qed.*)

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
  Definition column_to_poly : column -> poly byte := to_list.
  Definition poly_to_column (c : poly byte) : column :=
    resize_default fzero _ (of_list c).

  (* Modulus : x^4 + 1 *)
  Definition modulus := [x01; x00; x00; x00; x01].

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
  Import VectorNotations.
  Existing Instance byteops.

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
      



      
    PolyTheory.*)
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
  Add Ring fring : rtheory (morphism rmorph).

  Local Infix "+" := fadd.
  Local Infix "-" := fsub.
  Local Infix "*" := fmul.

  (* This odd property holds on bytes because add/sub are xors *)
  Lemma bytes_sub_is_add (a b : byte) :
    @fadd _ byteops a b = @fadd _ byteops a b.
  Proof. reflexivity. Qed.

  Definition sum (p : poly byte) : byte := fold_left fadd p fzero.
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
                                        (matrix_mulmod [x02;x01;x01;x03] (to_list c)).
  Proof.
    cbv [mix_single_column]. constant_vector_simpl c.
    autorewrite with push_to_list.
    autounfold with matrix_mulmod.
    cbv [of_list_sized of_list].
    rewrite resize_default_id.
    fequal_vector; ring.
  Qed.

  Lemma inv_mix_single_column_is_matrix_mulmod d c :
    inv_mix_single_column c = of_list_sized d 4%nat
                                        (matrix_mulmod [x0e;x09;x0d;x0b] (to_list c)).
  Proof.
    cbv [inv_mix_single_column]. constant_vector_simpl c.
    autorewrite with push_to_list.
    autounfold with matrix_mulmod.
    cbv [of_list_sized of_list].
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
    apply VectorUtils.map_id_ext.
    apply inverse_mix_single_column.
  Qed.
End Properties.
