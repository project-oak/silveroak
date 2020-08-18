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

From Coq Require Import Arith Eqdep_dec List Lia NArith Omega String.
From Arrow Require Import Category Kappa ClosureConversion.
From Cava Require Import BitArithmetic Arrow.CavaArrow Arrow.CavaExpression.

Import ListNotations.
Import EqNotations.

Declare Scope kappa_scope.
Declare Custom Entry expr.
Delimit Scope kappa_scope with kappa.

(* Kappa expression and application *)

Module KappaNotation.
  Notation "<[ e ]>" := (
    Closure_conversion (arrow:=CircuitArrow) (fun var => e%kappa)
   ) (at level 1, e custom expr at level 1).

  (* Notation "<[ e ]>" := (e%kappa) (at level 1, e custom expr at level 1). *)

  Notation "\ x .. y => e" := (Abs (fun x => .. (Abs (fun y => e)) ..))
    (in custom expr at level 200, x binder, right associativity
    (* , format "'[' \  '/  ' x  ..  y =>  '/  ' e ']'" *)
    )
                                    : kappa_scope.

  Notation "x y" := (App x y) (in custom expr at level 3, left associativity) : kappa_scope.

  Notation "x" := (Var x) (in custom expr, x ident) : kappa_scope.
  Notation "( x )" := x (in custom expr, x at level 4) : kappa_scope.
  Notation "'let' x = e1 'in' e2" := (Let e1 (fun x => e2)) (in custom expr at level 1, x constr at level 4, e2 at level 7, e1 at level 1) : kappa_scope.

  (* todo: turn into a recursive pattern *)
  Notation "'let' '( x , y ) = e1 'in' e2"
    := (
    Let (App kappa_fst e1) (fun x =>
      Let (App kappa_snd e1) (fun y => e2
      )
    )
    )
    (in custom expr at level 1, x constr at level 4, y constr at level 4, e2 at level 7, e1 at level 1) : kappa_scope.

  (* Escaping *)

  Notation "! x" := (Morph (x ))(in custom expr at level 2, x global) : kappa_scope.
  Notation "!( x )" := (Morph (x )) (in custom expr, x constr) : kappa_scope.

  Notation tupleHelper := (fun x y => App (App kappa_pair x) y).
  Notation "( x , .. , y , z )" := (
    (tupleHelper x .. (tupleHelper y z) .. )
    )
    (in custom expr, x at level 4, y at level 4, z at level 4) : kappa_scope.

  (* Pre defined functions *)

  Notation "'fst'" := (kappa_fst) (in custom expr at level 4) : kappa_scope.
  Notation "'snd'" := (kappa_snd) (in custom expr at level 4) : kappa_scope.

  Notation "'not'" := (Morph (Primitive not_gate)) (in custom expr at level 4) : kappa_scope.
  Notation "'and'" := (Morph (Primitive and_gate)) (in custom expr at level 4) : kappa_scope.
  Notation "'nand'" := (Morph (Primitive nand_gate)) (in custom expr at level 4) : kappa_scope.
  Notation "'or'" := (Morph (Primitive or_gate)) (in custom expr at level 4) : kappa_scope.
  Notation "'nor'" := (Morph (Primitive nor_gate)) (in custom expr at level 4) : kappa_scope.
  Notation "'xor'" := (Morph (Primitive xor_gate)) (in custom expr at level 4) : kappa_scope.
  Notation "'xnor'" := (Morph (Primitive xnor_gate)) (in custom expr at level 4) : kappa_scope.
  Notation "'buf'" := (Morph (Primitive buf_gate)) (in custom expr at level 4) : kappa_scope.
  Notation "'delay'" := (Morph (Primitive delay_gate)) (in custom expr at level 4) : kappa_scope.

  Notation "'xorcy'" := (Morph (Primitive xorcy)) (in custom expr at level 4) : kappa_scope.
  Notation "'muxcy'" := (Morph (Primitive muxcy)) (in custom expr at level 4) : kappa_scope.

  Definition unsigned_add2 {a b} := Primitive (unsigned_add a b (S (max a b))).
  Definition unsigned_add1 {a b} := Primitive (unsigned_add a b (max a b)).

  (* Notation "x + y" := (App (App (Morph (UnsignedAdd2 _ _)) x) y) (in custom expr at level 4) : kappa_scope. *)
  Notation "x + y" := 
      (App (App (Morph unsigned_add2) x) y) 
      (in custom expr at level 4) : kappa_scope.
  Notation "x +% y" := 
      (App (App (Morph unsigned_add1) x) y) 
      (in custom expr at level 4) : kappa_scope.
  Notation "x - y" := (App (App (Morph (Primitive (unsigned_sub _))) x) y) (in custom expr at level 4) : kappa_scope.
  Notation "'unsigned_add' a b c" := (Morph (Primitive (unsigned_add a b c)))
    (in custom expr at level 4,
    a constr at level 4,
    b constr at level 4,
    c constr at level 4
    ) : kappa_scope.
  Notation "'unsigned_sub' a" := (Morph (Primitive (unsigned_sub a)))
    (in custom expr at level 4,
    a constr at level 4
    ) : kappa_scope.

  Notation "'[]'" := (Morph (Primitive (empty_vec _))) (in custom expr at level 4) : kappa_scope.
  Notation "x ++ y" := (App (App (Morph (Primitive (concat _ _))) x) y) (in custom expr at level 4) : kappa_scope.
  Notation "x :: y" := (App (App (Morph (Primitive (cons _ _))) x) y) (in custom expr at level 7, right associativity) : kappa_scope.

  Notation "'true'" := (Morph (Primitive (constant true))) (in custom expr at level 2) : kappa_scope.
  Notation "'false'" := (Morph (Primitive (constant false))) (in custom expr at level 2) : kappa_scope.

  Notation "# x" := (Morph (Primitive (constant_bitvec _ x)))%N (in custom expr at level 2, x constr at level 4) : kappa_scope.

  Notation "v [ x ]" := (App (App (Morph (Primitive (index _ _))) v) x)
    ( in custom expr at level 2
    , x at level 7
    ) : kappa_scope.
  Notation "v [: x : y ]" :=
        (App (Morph (Primitive (slice _ (x <: nat) (y <: nat) _))) v)
    (in custom expr at level 2,
    (* v constr, *)
    x constr at level 7,
    y constr at level 7
    ) : kappa_scope.

  Notation "'index'" := (Morph (Primitive (index _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'empty'" := (Morph (Primitive (empty_vec))) (in custom expr at level 4) : kappa_scope.
  Notation "'cons'" := (Morph (Primitive (cons _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'snoc'" := (Morph (Primitive (snoc _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'concat'" := (Morph (Primitive (concat _ _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'split_at' x" := (Morph (Primitive (split x _ _))) (in custom expr at level 4, x constr at level 4) : kappa_scope.
  Notation "'uncons'" := (Morph (Primitive (uncons _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'unsnoc'" := (Morph (Primitive (unsnoc _ _))) (in custom expr at level 4) : kappa_scope.


End KappaNotation.

Definition make_module {i o}
  (name: string)
  (expr: i ~> o)
  : i ~> o
  := expr.
  (* mk_module _ _ name (expr _). *)

Import KappaNotation.
Local Open Scope kind_scope.

Section regression_examples.
  Import KappaNotation.
  Local Open Scope kappa_scope.

  Definition ex0_constant:  << Vector Bit 10, Unit >> ~> (Vector Bit 8)
    := <[ \x => x [: 7 : 0 ] ]>.

  Definition ex1_constant:  << Bit, Unit >> ~> Bit := <[ \x => true ]>.
  Definition ex2_parameterized (n: nat):  << Bit, Unit >> ~> Bit :=
  match n with
  | O => <[ \ x => true ]>
  | S n => <[ \ x => xor x x ]>
  end.

  Definition ex3_to_vec:  << Bit, Unit >> ~> (Vector Bit 1) :=
  <[ \ x => x :: [] ]>.
  Definition ex4_index_vec:  << Vector Bit 10, Unit >> ~> Bit :=
  <[ \ x => index x (# 1) ]>.
  Definition ex5_index_vec2:  << Vector Bit 10, Unit >> ~> Bit :=
  <[ \ x => x [# 1] ]>.
  Definition ex6_concat:  << Vector Bit 2, Bit, Unit >> ~> (Vector Bit 3) :=
  <[ \ x v => snoc x v ]>.
  Definition ex7_xor:  << Bit, Bit, Unit >> ~> Bit :=
  <[ \ x y => xor x y ]>.
  Definition ex7_tupled_destruct:  << << Bit, Bit>>, Unit>> ~> Bit :=
  <[ \ xy =>
    let '(x,y) = xy in
    y ]>.
  Definition ex8_multiindex:  << Vector (Vector Bit 5) 10, Unit >> ~> Bit :=
  <[ \ x => x[#0][#1] ]>.
  Definition ex9_mkvec:  << Bit, Unit >> ~> (Vector Bit 2) :=
  <[ \x => true :: false :: [] ]>.
  Definition ex10:  << Vector Bit 10, Vector Bit 10, Unit >> ~> (Vector Bit 11) :=
  <[ \ x y => x + y ]>.
  Definition ex11:  << Vector Bit 10, Vector Bit 10, Unit >> ~> (Vector Bit 10) :=
  <[ \ x y => x +% y ]>.
  Definition ex12_module:  <<Vector Bit 10, Unit>> ~> Vector Bit 10
    := make_module "ex12_module" <[ \x => x +% x ]>.
  Definition ex13:  << Vector Bit 10, Unit >> ~> Bit :=
  <[ \ x => (xor x[#0] x[#1] :: false :: []) [#0] ]>.
  Definition ex14:  << Vector Bit 10, Vector Bit 4, Unit >> ~> Bit :=
  <[ \ x i => x [ i ] ]>.

  Fixpoint copy_object_pow2 o (n:nat): Kind :=
  match n with
  | O => o
  | S n => Tuple (copy_object_pow2 o n) (copy_object_pow2 o n)
  end.

  Fixpoint tree
    (A: Kind)
    (n: nat)
    (f: << A, A, Unit >> ~> A)
    {struct n}
    :  << copy_object_pow2 A n, Unit >> ~> A :=
  match n with
  | O => <[ \ x => x ]>
  | S n' =>
    <[\ x =>
        let a = !(tree A n' f) (fst x) in
        let b = !(tree A n' f) (snd x) in
        !f a b
    ]>
  end.

  Definition add' (n: nat)
    :  <<Vector Bit n, Vector Bit n, Unit>> ~> (Vector Bit n)
    :=
    match Nat.eq_dec (Init.Nat.max n n) n with
    | left Heq => rew [fun x =>  _~>Vector Bit x] Heq in <[\x y=> x +% y]>
    | right Hneq => (ltac:(lia))
    end.

  Definition adder_tree
    (bitsize n: nat)
    : <<copy_object_pow2 (Vector Bit bitsize) n, Unit>> ~> (Vector Bit bitsize) :=
    tree (Vector Bit bitsize) n (add' bitsize).

  Definition xilinxFullAdder
    :  << Bit, << Bit, Bit >>, Unit>> ~> (Tuple Bit Bit) :=
    <[ \ cin ab =>
      let a = fst ab in
      let b = snd ab in
      let part_sum = xor a b in
      let sum      = xorcy part_sum cin in
      let cout     = muxcy part_sum (cin, a) in
      (sum, cout)
    ]>.

End regression_examples.
