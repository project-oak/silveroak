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

From Coq Require Import Arith Eqdep_dec List Lia NArith Omega.
From Arrow Require Import Category Kappa ClosureConversion.
From Cava Require Import BitArithmetic Arrow.CavaArrow Arrow.CavaExpression.

Import ListNotations.

Declare Scope kappa_scope.
Declare Custom Entry expr.
Delimit Scope kappa_scope with kappa.

(* Kappa expression and application *)

Module KappaNotation.
  Notation "<[ e ]>" := (e%kappa) (at level 1, e custom expr at level 1).

  Notation "\ x .. y => e" := (Abs (fun x => .. (Abs (fun y => e)) ..))
    (in custom expr at level 200, x binder, right associativity,
    format "'[' \  '/  ' x  ..  y =>  '/  ' e ']'")
                                    : kappa_scope.

  Notation "x y" := (App x y) (in custom expr at level 3, left associativity) : kappa_scope.

  Notation "x" := (Var x) (in custom expr, x ident) : kappa_scope.
  Notation "( x )" := x (in custom expr, x at level 4) : kappa_scope.
  Notation "'let' x = e1 'in' e2" := (Let e1 (fun x => e2)) (in custom expr at level 1, x constr at level 4, e2 at level 5, e1 at level 1) : kappa_scope.

  (* todo: turn into a recursive pattern *)
  Notation "'let' '( x , y ) = e1 'in' e2"
    := (
    Let (App Fst e1) (fun x =>
      Let (App Snd e1) (fun y => e2
      )
    )
    )
    (in custom expr at level 1, x constr at level 4, y constr at level 4, e2 at level 5, e1 at level 1) : kappa_scope.

  (* Escaping *)

  Notation "! x" := (x)(in custom expr at level 2, x global) : kappa_scope.
  Notation "!( x )" := (x) (in custom expr, x constr) : kappa_scope.

  Notation "( x , .. , y , z )" := (
    (tupleHelper x .. (tupleHelper y z) .. )
    )
    (in custom expr, x at level 4, y at level 4, z at level 4) : kappa_scope.

  (* Pre defined functions *)

  Notation "'fst'" := (Fst) (in custom expr at level 4) : kappa_scope.
  Notation "'snd'" := (Snd) (in custom expr at level 4) : kappa_scope.

  Notation "'not'" := (Not) (in custom expr at level 4) : kappa_scope.
  Notation "'and'" := (And) (in custom expr at level 4) : kappa_scope.
  Notation "'nand'" := (Nand) (in custom expr at level 4) : kappa_scope.
  Notation "'or'" := (Or) (in custom expr at level 4) : kappa_scope.
  Notation "'nor'" := (Nor) (in custom expr at level 4) : kappa_scope.
  Notation "'xor'" := (Xor) (in custom expr at level 4) : kappa_scope.
  Notation "'xnor'" := (Xnor) (in custom expr at level 4) : kappa_scope.
  Notation "'buf'" := (Buf) (in custom expr at level 4) : kappa_scope.
  Notation "'delay'" := (Delay) (in custom expr at level 4) : kappa_scope.

  Notation "'xorcy'" := (Xorcy) (in custom expr at level 4) : kappa_scope.
  Notation "'muxcy'" := (Muxcy) (in custom expr at level 4) : kappa_scope.

  Notation "'unsigned_add' a b c" := (UnsignedAdd a b c)
    (in custom expr at level 4,
    a constr at level 4,
    b constr at level 4,
    c constr at level 4
    ) : kappa_scope.
  Notation "x + y" := (App (App (UnsignedAdd2 _ _) x) y) (in custom expr at level 4) : kappa_scope.
  Notation "x +% y" := (App (App (UnsignedAdd1 _ _) x) y) (in custom expr at level 4) : kappa_scope.

  Notation "'index'" := (Index _) (in custom expr at level 4) : kappa_scope.
  Notation "'empty'" := (EmptyVec) (in custom expr at level 4) : kappa_scope.
  Notation "'cons'" := (Cons _) (in custom expr at level 4) : kappa_scope.
  Notation "'snoc'" := (Snoc _) (in custom expr at level 4) : kappa_scope.
  Notation "'concat'" := (Concat _ _) (in custom expr at level 4) : kappa_scope.
  Notation "'split_at' x" := (Split _ x _) (in custom expr at level 4, x constr at level 4) : kappa_scope.
  Notation "'uncons'" := (Uncons _) (in custom expr at level 4) : kappa_scope.
  Notation "'unsnoc'" := (Unsnoc _) (in custom expr at level 4) : kappa_scope.

  Notation "'[]'" := (EmptyVec) (in custom expr at level 4) : kappa_scope.
  Notation "v [ x ]" := (App (App (Index _) v) x) (in custom expr at level 4) : kappa_scope.
  Notation "x ++ y" := (App (App (Concat _ _) x) y) (in custom expr at level 4) : kappa_scope.
  Notation "x :: y" := (App (App (Cons _) x) y) (in custom expr at level 4) : kappa_scope.

  Notation "'true'" := (@LiftConstant _ Bit true) (in custom expr at level 2) : kappa_scope.
  Notation "'false'" := (@LiftConstant _ Bit false) (in custom expr at level 2) : kappa_scope.

  Notation "# x" := (@LiftConstant _ (Vector Bit _) x)%N (in custom expr at level 2, x constr at level 4) : kappa_scope.


  Notation " v [ x : y ] " :=
        (App (Slice _ x y _ _) v)
    (in custom expr at level 4,
    v constr,
    x constr at level 5,
    y constr at level 5
    ) : kappa_scope.

  Notation "'vector' { }" := ( EmptyVec ) (in custom expr at level 4) : kappa_scope.
  Notation "'vector' { x , .. , y }" :=
    (App (App (Snoc _) .. (App (App (Snoc _) EmptyVec) x) ..) y) (in custom expr at level 4) : kappa_scope.
End KappaNotation.

Notation "'to_arrow' circuit" := (
  insert_rightmost_tt1 _ >>> 
  closure_conversion (object_decidable_equality:=decKind) (Desugar (circuit)) (ltac:(simpl;tauto))
)(at level 100).


Section regression_examples.
  Import KappaNotation.
  Local Open Scope kappa_scope.

  Context {var: Kind -> Kind -> Type}.

  Definition ex0_constant: CavaExpr var << Vector Bit 10, Unit >> (Vector Bit 8).
    refine (<[ \x => x [ 7 : 0 ] ]>); lia.
  Defined.

  Definition ex1_constant: CavaExpr var << Bit, Unit >> Bit := <[ \x => true ]>.
  Definition ex2_parameterized (n: nat): CavaExpr var << Bit, Unit >> Bit :=
  match n with
  | O => <[ \ x => true ]>
  | S n => <[ \ x => xor x x ]>
  end.

  Definition ex3_to_vec: CavaExpr var << Bit, Unit >> (Vector Bit 1) :=
  <[ \ x => vector { x } ]>.
  Definition ex4_index_vec: CavaExpr var << Vector Bit 10, Unit >> Bit :=
  <[ \ x => index x (# 1) ]>.
  Definition ex5_index_vec2: CavaExpr var << Vector Bit 10, Unit >> Bit :=
  <[ \ x => x [# 1] ]>.
  Definition ex6_concat: CavaExpr var << Vector Bit 2, Bit, Unit >> (Vector Bit 3) :=
  <[ \ x v => snoc x v ]>.
  Definition ex7_xor: CavaExpr var << Bit, Bit, Unit >> Bit :=
  <[ \ x y => xor x y ]>.
  Definition ex7_tupled_destruct: CavaExpr var << << Bit, Bit>>, Unit>> Bit :=
  <[ \ xy =>
    let '(x,y) = xy in
    y ]>.
  Definition ex8_multiindex: CavaExpr var << Vector (Vector Bit 5) 10, Unit >> Bit :=
  <[ \ x => x[#0][#1] ]>.
  Definition ex9_mkvec: CavaExpr var << Bit, Unit >> (Vector Bit 2) :=
  <[ \x => vector { true, false } ]>.
  Definition ex10: CavaExpr var << Vector Bit 10, Vector Bit 10, Unit >> (Vector Bit 11) :=
  <[ \ x y => x + y ]>.
  Definition ex11: CavaExpr var << Vector Bit 10, Vector Bit 10, Unit >> (Vector Bit 10) :=
  <[ \ x y => x +% y ]>.

  Fixpoint copy_object_pow2 o (n:nat): Kind :=
  match n with
  | O => o
  | S n => Tuple (copy_object_pow2 o n) (copy_object_pow2 o n)
  end.

  Fixpoint tree
    (A: Kind)
    (n: nat)
    (f: CavaExpr var << A, A, Unit >> A)
    {struct n}
    : CavaExpr var << copy_object_pow2 A n, Unit >> A :=
  match n with
  | O => <[ \ x => x ]>
  | S n' =>
    <[\ x =>
        let a = !(tree A n' f) (fst x) in
        let b = !(tree A n' f) (snd x) in
        !f a b
    ]>
  end.

  Definition xilinxFullAdder
    : CavaExpr var << Bit, << Bit, Bit >>, Unit>> (Tuple Bit Bit) :=
    <[ \ cin ab =>
      let a = fst ab in
      let b = snd ab in
      let part_sum = xor a b in
      let sum      = xorcy part_sum cin in
      let cout     = muxcy part_sum (cin, a) in
      (sum, cout)
    ]>.

  Definition adder_tree
    (bitsize n: nat)
    : CavaExpr var <<copy_object_pow2 (Vector Bit bitsize) n, Unit>> (Vector Bit bitsize) :=
    tree (Vector Bit bitsize) n (UnsignedAdd _ _ _).

End regression_examples.
