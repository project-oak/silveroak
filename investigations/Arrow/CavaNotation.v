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

Require Import Coq.Arith.Arith Coq.Lists.List
     Coq.NArith.NArith Coq.Strings.String.
Require Import Cava.BitArithmetic Cava.Arrow.ExprSyntax.
Require Import Cava.Arrow.Primitives.

Import ListNotations.
Import EqNotations.

Declare Scope kappa_scope.
Declare Custom Entry expr.
Delimit Scope kappa_scope with kappa.

Set Implicit Arguments.
Generalizable All Variables.

(* Kappa expression and application *)

Module KappaNotation.

  Notation "<[ 'fun' name x .. y : ret => e ]>" := (
    mkModule name (fun var =>
      (Abs (fun x => .. (Abs (fun y => e)) ..)) : kappa var _ ret
    )%kappa : ModuleK _ _
   ) (at level 1, name constr at level 1, x closed binder, e custom expr at level 99).

  Notation "<[ \ x .. y => e ]>" := (
    mkModule "" (fun var =>
    (Abs (fun x => .. (Abs (fun y => e)) ..)) : kappa var _ _
    )%kappa: ModuleK _ _
   ) (at level 1, x closed binder, e custom expr at level 1).

  Notation "<[ \ x .. y : ret => e ]>" := (
    mkModule "" (fun var =>
    (Abs (fun x => .. (Abs (fun y => e)) ..)) : kappa var _ ret
    )%kappa: ModuleK _ _
   ) (at level 1, x closed binder, e custom expr at level 1).

  Notation "<[ e ]>" := (
    mkModule "" (fun var => e%kappa): ModuleK _ _
   ) (at level 1, e custom expr at level 99).

  Notation "x ~> y" := (ModuleK x y) (at level 90).

  Notation "x y" := (App x y) (in custom expr at level 3, left associativity) : kappa_scope.

  Notation "x" := (Var x) (in custom expr, x ident) : kappa_scope.
  Notation "( x )" := x (in custom expr, x at level 4) : kappa_scope.
  Notation "'let' x = a 'in' b" := (Let a (fun x => b))
    (in custom expr at level 1, x constr at level 4, b at level 7, a at level 1) : kappa_scope.
  Notation "'let' x : ty = a 'in' b" := (Let a (fun x : _ Unit ty => b))
    (in custom expr at level 1, x constr at level 4, b at level 7, ty constr at level 7, a at level 1) : kappa_scope.
  Notation "'letrec' x = a 'in' b" := (LetRec (fun x => a) (fun x => b))
    (in custom expr at level 1, x constr at level 4, b at level 7, a at level 1) : kappa_scope.

  (* destructuring *)
  Notation "'let' '( x , .. , y ) : ty = a 'in' e" := (
    Let (a : kappa _ Unit ty) (fun a_var => Comp1
      (Abs (fun x => .. (Abs (fun y => e)) ..) )
      (Var a_var : kappa _ Unit ty)
    ) )
    ( in custom expr at level 1, x closed binder, ty constr at level 7, e at level 7) : kappa_scope.

  Notation "'let' '( x , .. , y ) = a 'in' e" := (
    Let a (fun a_var => Comp1
      (Abs (fun x => .. (Abs (fun y => e)) ..) )
      (Var a_var )
    ) )
    ( in custom expr at level 1, x closed binder, e at level 7) : kappa_scope.

  (* Escaping *)

  Notation "! x" := (CallModule x)(in custom expr at level 2, x global) : kappa_scope.
  Notation "!( x )" := (CallModule x)(in custom expr, x constr) : kappa_scope.

  Notation tupleHelper := (fun x y => App (App (Primitive (P2 (Pair _ _))) x) y).
  Notation "( x , .. , y , z )" := (
    (tupleHelper x .. (tupleHelper y z) .. )
    )
    (in custom expr, x at level 4, y at level 4, z at level 4) : kappa_scope.

  (* Pre defined functions *)

  Notation "'typecast'" := (Typecast _ _) (in custom expr at level 4) : kappa_scope.

  Notation "'fst'" := (Primitive (P1 (Fst _ _ ))) (in custom expr at level 4) : kappa_scope.
  Notation "'snd'" := (Primitive (P1 (Snd _ _ ))) (in custom expr at level 4) : kappa_scope.

  Notation "'not'" := (Primitive (P1 Not)) (in custom expr at level 4) : kappa_scope.
  Notation "'and'" := (Primitive (P2 And)) (in custom expr at level 4) : kappa_scope.
  Notation "'nand'" := (Primitive (P2 Nand)) (in custom expr at level 4) : kappa_scope.
  Notation "'or'" := (Primitive (P2 Or)) (in custom expr at level 4) : kappa_scope.
  Notation "'nor'" := (Primitive (P2 Nor)) (in custom expr at level 4) : kappa_scope.
  Notation "'xor'" := (Primitive (P2 Xor)) (in custom expr at level 4) : kappa_scope.
  Notation "'xnor'" := (Primitive (P2 Xnor)) (in custom expr at level 4) : kappa_scope.
  Notation "'buf'" := (Primitive (P1 BufGate)) (in custom expr at level 4) : kappa_scope.
  Notation "'delay'" := (ExprSyntax.Delay) (in custom expr at level 4) : kappa_scope.

  Notation "'xorcy'" := (Primitive (P2 Xorcy)) (in custom expr at level 4) : kappa_scope.
  Notation "'muxcy'" := (Primitive (P2 Muxcy)) (in custom expr at level 4) : kappa_scope.

  Definition unsigned_add2 {var a b} := Primitive (var:=var) (P2 (UnsignedAdd a b (S (max a b)))).
  Definition unsigned_add1 {var a} := Primitive (var:=var) (P2 (UnsignedAdd a a a)).

  Notation "x + y" :=
      (App (App unsigned_add2 x) y)
      (in custom expr at level 4) : kappa_scope.
  Notation "x +% y" :=
      (App (App unsigned_add1 x) y)
      (in custom expr at level 4) : kappa_scope.
  Notation "x - y" := (App (App ((Primitive (P2 (UnsignedSub _)))) x) y) (in custom expr at level 4) : kappa_scope.
  Notation "'unsigned_add' a b c" := ((Primitive (P2 (UnsignedAdd a b c))))
    (in custom expr at level 4,
    a constr at level 4,
    b constr at level 4,
    c constr at level 4
    ) : kappa_scope.
  Notation "'unsigned_sub' a" := ((Primitive (P2 (UnsignedSub a))))
    (in custom expr at level 4,
    a constr at level 4
    ) : kappa_scope.
  Notation "x * y" :=
      (App (App (Primitive (P2 (Mult _ _))) x) y)
      (in custom expr at level 4) : kappa_scope.

  Notation "'[]'" := (Primitive (P0 (EmptyVec _))) (in custom expr at level 4) : kappa_scope.
  Notation "x ++ y" := (App (App (Primitive (P2 (Concat _ _))) x) y) (in custom expr at level 4) : kappa_scope.
  Notation "x :: y" := (App (App (Primitive (P2 (Cons _ _))) x) y) (in custom expr at level 7, right associativity) : kappa_scope.

  Notation "'true''" := (Primitive (P0 (Constant Bit true))) (in custom expr at level 2) : kappa_scope.
  Notation "'false''" := (Primitive (P0 (Constant Bit false))) (in custom expr at level 2) : kappa_scope.

  Notation "# x" := (Primitive (P0 (Constant (Vector Bit _) (N2Bv_sized _ x))))%N
    (in custom expr at level 2,
    x constr at level 4, no associativity) : kappa_scope.


  Notation "{ x , y , .. , z }" :=
    (
      let ls := (cons x (cons y .. (cons z nil) ..)) in
      (Primitive (P0
      (ConstantVec
        (List.length ls)
        (Vector Bit _)
        (List.map (N2Bv_sized _) ls)
      ))))%list%N
    (in custom expr at level 2,
    x constr at level 4, y constr at level 4, z constr at level 4, no associativity) : kappa_scope.

  Notation "v [ x ]" := (App (App (Primitive (P2 (Index _ _))) v) x)
    ( in custom expr at level 2
    , x at level 7
    ) : kappa_scope.
  Notation "v [: x : y ]" :=
        (App (Primitive (P1 (Slice _ (x <: nat) (y <: nat) _))) v)
    (in custom expr at level 2,
    (* v constr, *)
    x constr at level 7,
    y constr at level 7
    ) : kappa_scope.

  Notation "'index'" := (Primitive (P2 (Index _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'empty'" := (Primitive (P0 EmptyVec)) (in custom expr at level 4) : kappa_scope.
  Notation "'cons'" := (Primitive (P2 (Cons _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'snoc'" := (Primitive (P2 (Snoc _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'concat'" := (Primitive (P2 (Concat _ _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'split_at' x" := (Primitive (P1 (Split x _ _))) (in custom expr at level 4, x constr at level 4) : kappa_scope.
  Notation "'uncons'" := (Primitive (P1 (Uncons _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'unsnoc'" := (Primitive (P1 (Unsnoc _ _))) (in custom expr at level 4) : kappa_scope.

End KappaNotation.

Section regression_examples.
  Import KappaNotation.
  Local Open Scope kappa_scope.

  Definition ex0_constant
    := <[ fun "ex0_constant" ( x : _ (Vector Bit 8) ) : Vector Bit 8 => x [: 7 : 0 ] ]>.

  Definition ex1_constant: << Bit, Unit >> ~> Bit := <[ \ x => true' ]> .

  Definition ex2_parameterized (n: nat): << Bit, Unit >> ~> Bit :=
  match n with
  | O => <[\x => true' ]>
  | S n => <[\x => xor x x ]>
  end.

  Definition ex3_to_vec: << Bit, Unit >> ~> (Vector Bit 1) :=
  <[ \ x => x :: [] ]>.
  Definition ex4_index_vec: << Vector Bit 10, Unit >> ~> Bit :=
  <[ \ x => index x (# 1) ]>.
  Definition ex5_index_vec2: << Vector Bit 10, Unit >> ~> Bit :=
  <[ \ x => x [# 1] ]>.
  Definition ex6_concat: << Vector Bit 2, Bit, Unit >> ~> (Vector Bit 3) :=
  <[ \ x v => snoc x v ]>.

  Definition ex7_xor :=
    <[fun "ex7_xor" (x : _ Bit) (y : _ Bit) : Bit => let z = xor x y in z ]>.

  Definition ex7_tupled_destruct: << << Bit, Bit>>, Unit>> ~> Bit :=
  <[ \ xy =>
    let '(x,y) : <<Bit,Bit>> = xy in
    y ]>.
  Definition ex8_multiindex: << Vector (Vector Bit 5) 10, Unit >> ~> Bit :=
  <[ \ x => x[#0][#1] ]>.
  Definition ex9_mkvec: << Bit, Unit >> ~> (Vector Bit 2) :=
  <[ \x => true' :: false' :: [] ]>.
  Definition ex10: << Vector Bit 10, Vector Bit 10, Unit >> ~> (Vector Bit 11) :=
  <[ \ x y => x + y ]>.
  Definition ex11: << Vector Bit 10, Vector Bit 10, Unit >> ~> (Vector Bit 10) :=
  <[ \ x y => x +% y ]>.
  Definition ex13: << Vector Bit 10, Unit >> ~> Bit :=
  <[ \ x => (xor x[#0] x[#1] :: false' :: []) [#0] ]>.
  Definition ex14: << Vector Bit 10, Vector Bit 4, Unit >> ~> Bit :=
  <[ \ x i => x [ i ] ]>.
  Definition ex15_rec_xor: << Bit, Unit >> ~> Bit :=
  <[ \ x => letrec s = delay (xor x s) in s ]>.
  Definition ex16_triple: << <<Bit, Bit, Bit>>, Unit >> ~> Bit :=
  <[ \ triple => let '(x, y, z) : <<Bit,Bit,Bit>> = triple in x ]>.
  Definition ex17_constant_via_list: << Unit >> ~> (Vector (Vector Bit 4) 3) := <[ { 1, 2, 3 } ]>.

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
    : << copy_object_pow2 A n, Unit >> ~> A :=
  match n with
  | O =>
    <[ \ x => x ]>
  | S n' =>
    <[\ x =>
        let a = !(tree n' f) (fst x) in
        let b = !(tree n' f) (snd x) in
        !f a b
    ]>
  end.

  Definition adder_tree
    (bitsize n: nat)
    : <<copy_object_pow2 (Vector Bit bitsize) n, Unit>> ~> (Vector Bit bitsize) :=
    <[ !(tree n <[\x y => x +% y]> ) ]>.

  Definition xilinxFullAdder
    : << Bit, << Bit, Bit >>, Unit>> ~> (Tuple Bit Bit) :=
    <[ \ cin ab =>
      let a = fst ab in
      let b = snd ab in
      let part_sum = xor a b in
      let sum      = xorcy part_sum cin in
      let cout     = muxcy part_sum (cin, a) in
      (sum, cout)
    ]>.

  Fixpoint reshape {n m A}
    : << Vector A (n * m), Unit >> ~> << Vector (Vector A m) n >> :=
  match n with
  | 0 => <[\_ => [] ]>
  | S n' =>
    <[ \vec =>
      let '(x, xs) : <<Vector A _, Vector A _>> = split_at m vec in
      x :: !(@reshape n' m A) xs
      ]>
  end.

  Definition dummy {T}
    : << Bit, T, T, Unit >> ~> <<T>> :=
    <[\_ x _ => x]>.
  Notation T:=(Bit )(only parsing).
  Notation "'if' i 'then' t 'else' e" :=
    (App (App (App (CallModule dummy) i) t) e)
    (in custom expr at level 5, left associativity) : kappa_scope.

  Definition exfailed: << <<T,T>>,<<T,T>>, Unit >> ~> <<T,T>> :=
    <[\s1 s2 =>
    let '(a,b) : <<_,T>> =  s1 in
    let '(aa,bb) : <<_,T>> = s2 in
    if a then (a,b) else s1
    ]>.

End regression_examples.

