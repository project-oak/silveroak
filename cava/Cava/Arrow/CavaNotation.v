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
From Cava Require Import Arrow.Classes.Category.
From Cava Require Import BitArithmetic Arrow.CircuitArrow Arrow.ExprSyntax.
From Cava Require Import Arrow.ArrowKind.
From Cava Require Import Arrow.Primitives.

Import ListNotations.
Import EqNotations.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

Declare Scope kappa_scope.
Declare Custom Entry expr.
Delimit Scope kappa_scope with kappa.

(* Kappa expression and application *)

Module KappaNotation.
  Notation "<[ e ]>" := (
    (fun var => e%kappa)
   ) (at level 1, e custom expr at level 1).

  Notation "\ x .. y => e" := (Abs (fun x => .. (Abs (fun y => e)) ..))
    (in custom expr at level 200, x binder, right associativity) : kappa_scope.

  Notation "x y" := (App x y) (in custom expr at level 3, left associativity) : kappa_scope.

  Notation "x" := (Var x) (in custom expr, x ident) : kappa_scope.
  Notation "( x )" := x (in custom expr, x at level 4) : kappa_scope.
  Notation "'let' x = a 'in' b" := (Let a (fun x => b))
    (in custom expr at level 1, x constr at level 4, b at level 7, a at level 1) : kappa_scope.
  Notation "'let' x : ty = a 'in' b" := (Let a (fun x : _ Unit ty => b))
    (in custom expr at level 1, x constr at level 4, b at level 7, ty constr at level 7, a at level 1) : kappa_scope.
  Notation "'letrec' x = a 'in' b" := (LetRec (fun x => a) (fun x => b))
    (in custom expr at level 1, x constr at level 4, b at level 7, a at level 1) : kappa_scope.

  (* TODO(blaxill): can this be turned into a recursive pattern?
  The binders not mentioned on the lhs (e.g. a_binder) prevent me from doing this
  I think. Moving away from PHOAS would also work *)

  (* This function shouldn't be necessary but helps with type unification when
  using the tuple destructuring notation *)
  Definition proj1_tuple1 ty: CircuitPrimitive :=
    match ty with
    | Tuple l r => Fst l r
    | _ => Fst Unit Unit
    end.

  Notation "'let' '( x , y ) = a 'in' b" := (
    Let a (fun a_binder =>
    Let (App (Primitive (Fst _ _)) (Var a_binder)) (fun x =>
      Let (App (Primitive (Snd _ _)) (Var a_binder)) (fun y => b))))
    ( in custom expr at level 1, x constr, y constr, b at level 7) : kappa_scope.

  Notation "'let' '( x , y ) : ty = a 'in' b" := (
    Let a (fun a_binder =>
    Let (App (Primitive (proj1_tuple1 ty)) (Var a_binder)) (fun x =>
      Let (App (Primitive (Snd _ _ )) (Var a_binder)) (fun y => b))))
    ( in custom expr at level 1, x constr, y constr, ty constr at level 7, b at level 7) : kappa_scope.

  Notation "'let' '( x , y , z ) = a 'in' b" := (
    Let a (fun a_binder =>
    Let (App (Primitive (Fst _ _ )) (Var a_binder)) (fun x =>
      Let (App (Primitive (Snd _ _ )) (Var a_binder)) (fun a_tl_binder =>
        Let (App (Primitive (Fst _ _ )) (Var a_tl_binder)) (fun y =>
          Let (App (Primitive (Snd _ _ )) (Var a_tl_binder)) (fun z =>
          b))))))
    ( in custom expr at level 1, x constr, y constr, z constr, b at level 7) : kappa_scope.
  Notation "'let' '( x , y , z , w ) = a 'in' b" := (
    Let a (fun a_binder =>
    Let (App (Primitive (Fst _ _ )) (Var a_binder)) (fun x =>
      Let (App (Primitive (Snd _ _ )) (Var a_binder)) (fun a_tl_binder =>
        Let (App (Primitive (Fst _ _ )) (Var a_tl_binder)) (fun y =>
            Let (App (Primitive (Snd _ _ )) (Var a_tl_binder)) (fun a_tl_tl_binder =>
              Let (App (Primitive (Fst _ _ )) (Var a_tl_tl_binder)) (fun z =>
                Let (App (Primitive (Snd _ _ )) (Var a_tl_tl_binder)) (fun w =>
          b))))))))
    ( in custom expr at level 1, x constr, y constr, z constr, w constr, b at level 7) : kappa_scope.
  Notation "'let' '( x1 , x2 , x3 , x4 , x5 ) = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (Fst _ _ )) (Var binder1)) (fun x1 =>
      Let (App (Primitive (Snd _ _ )) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (Fst _ _ )) (Var binder2)) (fun x2 =>
            Let (App (Primitive (Snd _ _ )) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (Fst _ _ )) (Var binder3)) (fun x3 =>
                Let (App (Primitive (Snd _ _ )) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (Fst _ _ )) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (Snd _ _ )) (Var binder4)) (fun x5 =>
          b))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr
    , b at level 7) : kappa_scope.
  Notation "'let' '( x1 , x2 , x3 , x4 , x5 , x6 ) = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (Fst _ _ )) (Var binder1)) (fun x1 =>
      Let (App (Primitive (Snd _ _ )) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (Fst _ _ )) (Var binder2)) (fun x2 =>
            Let (App (Primitive (Snd _ _ )) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (Fst _ _ )) (Var binder3)) (fun x3 =>
                Let (App (Primitive (Snd _ _ )) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (Fst _ _ )) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (Snd _ _ )) (Var binder4)) (fun binder5 =>
                      Let (App (Primitive (Fst _ _ )) (Var binder5)) (fun x5 =>
                        Let (App (Primitive (Snd _ _ )) (Var binder5)) (fun x6 =>
          b))))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr, x6 constr
    , b at level 7) : kappa_scope.
  Notation "'let' '( x1 , x2 , x3 , x4 , x5 , x6 , x7 ) = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (Fst _ _ )) (Var binder1)) (fun x1 =>
      Let (App (Primitive (Snd _ _ )) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (Fst _ _ )) (Var binder2)) (fun x2 =>
            Let (App (Primitive (Snd _ _ )) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (Fst _ _ )) (Var binder3)) (fun x3 =>
                Let (App (Primitive (Snd _ _ )) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (Fst _ _ )) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (Snd _ _ )) (Var binder4)) (fun binder5 =>
                      Let (App (Primitive (Fst _ _ )) (Var binder5)) (fun x5 =>
                        Let (App (Primitive (Snd _ _ )) (Var binder5)) (fun binder6 =>
                            Let (App (Primitive (Fst _ _ )) (Var binder6)) (fun x6 =>
                              Let (App (Primitive (Snd _ _ )) (Var binder6)) (fun x7 =>
          b))))))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr, x6 constr, x7 constr
    , b at level 7) : kappa_scope.

  Notation "'let' '( x1 , x2 , x3 , x4 , x5 , x6 , x7 ) : ty = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (proj1_tuple1 ty)) (Var binder1)) (fun x1 =>
      Let (App (Primitive (Snd _ _ )) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (Fst _ _ )) (Var binder2)) (fun x2 =>
            Let (App (Primitive (Snd _ _ )) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (Fst _ _ )) (Var binder3)) (fun x3 =>
                Let (App (Primitive (Snd _ _ )) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (Fst _ _ )) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (Snd _ _ )) (Var binder4)) (fun binder5 =>
                      Let (App (Primitive (Fst _ _ )) (Var binder5)) (fun x5 =>
                        Let (App (Primitive (Snd _ _ )) (Var binder5)) (fun binder6 =>
                            Let (App (Primitive (Fst _ _ )) (Var binder6)) (fun x6 =>
                              Let (App (Primitive (Snd _ _ )) (Var binder6)) (fun x7 =>
          b))))))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr, x6 constr, x7 constr
    , ty constr at level 7
    , b at level 7) : kappa_scope.

  Notation "'let' '( x1 , x2 , x3 , x4 , x5 , x6 , x7 , x8 ) : ty = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (proj1_tuple1 ty)) (Var binder1)) (fun x1 =>
      Let (App (Primitive (Snd _ _ )) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (Fst _ _ )) (Var binder2)) (fun x2 =>
            Let (App (Primitive (Snd _ _ )) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (Fst _ _ )) (Var binder3)) (fun x3 =>
                Let (App (Primitive (Snd _ _ )) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (Fst _ _ )) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (Snd _ _ )) (Var binder4)) (fun binder5 =>
                      Let (App (Primitive (Fst _ _ )) (Var binder5)) (fun x5 =>
                        Let (App (Primitive (Snd _ _ )) (Var binder5)) (fun binder6 =>
                            Let (App (Primitive (Fst _ _ )) (Var binder6)) (fun x6 =>
                              Let (App (Primitive (Snd _ _ )) (Var binder6)) (fun binder7 =>
                                  Let (App (Primitive (Fst _ _ )) (Var binder7)) (fun x7 =>
                                    Let (App (Primitive (Snd _ _ )) (Var binder7)) (fun x8 =>
          b))))))))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr, x6 constr, x7 constr, x8 constr
    , ty constr at level 7
    , b at level 7) : kappa_scope.

  (* Escaping *)

  Notation "! x" := (RemoveContext (x _))(in custom expr at level 2, x global) : kappa_scope.
  Notation "!( x )" := (RemoveContext (x _)) (in custom expr, x constr) : kappa_scope.

  Notation tupleHelper := (fun x y => App (App (Primitive (Pair _ _)) x) y).
  Notation "( x , .. , y , z )" := (
    (tupleHelper x .. (tupleHelper y z) .. )
    )
    (in custom expr, x at level 4, y at level 4, z at level 4) : kappa_scope.

  (* Pre defined functions *)

  Notation "'fst'" := (Primitive (Fst _ _ )) (in custom expr at level 4) : kappa_scope.
  Notation "'snd'" := (Primitive (Snd _ _ )) (in custom expr at level 4) : kappa_scope.

  Notation "'not'" := (Primitive Not) (in custom expr at level 4) : kappa_scope.
  Notation "'and'" := (Primitive And) (in custom expr at level 4) : kappa_scope.
  Notation "'nand'" := (Primitive Nand) (in custom expr at level 4) : kappa_scope.
  Notation "'or'" := (Primitive Or) (in custom expr at level 4) : kappa_scope.
  Notation "'nor'" := (Primitive Nor) (in custom expr at level 4) : kappa_scope.
  Notation "'xor'" := (Primitive Xor) (in custom expr at level 4) : kappa_scope.
  Notation "'xnor'" := (Primitive Xnor) (in custom expr at level 4) : kappa_scope.
  Notation "'buf'" := (Primitive BufGate) (in custom expr at level 4) : kappa_scope.
  Notation "'delay'" := (Primitive (Delay _)) (in custom expr at level 4) : kappa_scope.

  Notation "'xorcy'" := (Primitive Xorcy) (in custom expr at level 4) : kappa_scope.
  Notation "'muxcy'" := (Primitive Muxcy) (in custom expr at level 4) : kappa_scope.

  Definition unsigned_add2 {var a b} := Primitive (var:=var) (UnsignedAdd a b (S (max a b))).
  Definition unsigned_add1 {var a} := Primitive (var:=var) (UnsignedAdd a a a).

  Notation "x + y" :=
      (App (App unsigned_add2 x) y)
      (in custom expr at level 4) : kappa_scope.
  Notation "x +% y" :=
      (App (App unsigned_add1 x) y)
      (in custom expr at level 4) : kappa_scope.
  Notation "x - y" := (App (App ((Primitive (UnsignedSub _))) x) y) (in custom expr at level 4) : kappa_scope.
  Notation "'unsigned_add' a b c" := ((Primitive (UnsignedAdd a b c)))
    (in custom expr at level 4,
    a constr at level 4,
    b constr at level 4,
    c constr at level 4
    ) : kappa_scope.
  Notation "'unsigned_sub' a" := ((Primitive (UnsignedSub a)))
    (in custom expr at level 4,
    a constr at level 4
    ) : kappa_scope.

  Notation "'[]'" := ((Primitive (EmptyVec _))) (in custom expr at level 4) : kappa_scope.
  Notation "x ++ y" := (App (App ((Primitive (Concat _ _))) x) y) (in custom expr at level 4) : kappa_scope.
  Notation "x :: y" := (App (App ((Primitive (Cons _ _))) x) y) (in custom expr at level 7, right associativity) : kappa_scope.

  Notation "'true''" := ((Primitive (Constant Bit true))) (in custom expr at level 2) : kappa_scope.
  Notation "'false''" := ((Primitive (Constant Bit false))) (in custom expr at level 2) : kappa_scope.

  Notation "# x" := ((Primitive (Constant (Vector Bit _) (N2Bv_sized _ x))))%N
    (in custom expr at level 2,
    x constr at level 4, no associativity) : kappa_scope.


  Notation "{ x , y , .. , z }" :=
    (
      let ls := (cons x (cons y .. (cons z nil) ..)) in
      (Primitive
      (ConstantVec
        (List.length ls)
        (Vector Bit _)
        (List.map (N2Bv_sized _) ls)
      )))%list%N
    (in custom expr at level 2,
    x constr at level 4, y constr at level 4, z constr at level 4, no associativity) : kappa_scope.

  Notation "v [ x ]" := (App (App ((Primitive (Index _ _))) v) x)
    ( in custom expr at level 2
    , x at level 7
    ) : kappa_scope.
  Notation "v [: x : y ]" :=
        (App ((Primitive (Slice _ (x <: nat) (y <: nat) _))) v)
    (in custom expr at level 2,
    (* v constr, *)
    x constr at level 7,
    y constr at level 7
    ) : kappa_scope.

  Notation "'index'" := ((Primitive (Index _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'empty'" := ((Primitive EmptyVec)) (in custom expr at level 4) : kappa_scope.
  Notation "'cons'" := ((Primitive (Cons _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'snoc'" := ((Primitive (Snoc _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'concat'" := ((Primitive (Concat _ _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'split_at' x" := ((Primitive (Split x _ _))) (in custom expr at level 4, x constr at level 4) : kappa_scope.
  Notation "'uncons'" := ((Primitive (Uncons _ _))) (in custom expr at level 4) : kappa_scope.
  Notation "'unsnoc'" := ((Primitive (Unsnoc _ _))) (in custom expr at level 4) : kappa_scope.

End KappaNotation.

Import KappaNotation.
Local Open Scope kind_scope.

Section regression_examples.
  Import KappaNotation.
  Local Open Scope kappa_scope.

  Definition ex0_constant:  << Vector Bit 10, Unit >> ~[KappaCat]~> (Vector Bit 8)
    := <[ \x => x [: 7 : 0 ] ]>.


  Definition ex1_constant:  << Bit, Unit >> ~> Bit := <[ \x => true' ]>.
  Definition ex2_parameterized (n: nat):  << Bit, Unit >> ~> Bit :=
  match n with
  | O => <[ \ x => true' ]>
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
    let '(x,y) : <<Bit,Bit>> = xy in
    y ]>.
  Definition ex8_multiindex:  << Vector (Vector Bit 5) 10, Unit >> ~> Bit :=
  <[ \ x => x[#0][#1] ]>.
  Definition ex9_mkvec:  << Bit, Unit >> ~> (Vector Bit 2) :=
  <[ \x => true' :: false' :: [] ]>.
  Definition ex10:  << Vector Bit 10, Vector Bit 10, Unit >> ~> (Vector Bit 11) :=
  <[ \ x y => x + y ]>.
  Definition ex11:  << Vector Bit 10, Vector Bit 10, Unit >> ~> (Vector Bit 10) :=
  <[ \ x y => x +% y ]>.
  Definition ex13:  << Vector Bit 10, Unit >> ~> Bit :=
  <[ \ x => (xor x[#0] x[#1] :: false' :: []) [#0] ]>.
  Definition ex14:  << Vector Bit 10, Vector Bit 4, Unit >> ~> Bit :=
  <[ \ x i => x [ i ] ]>.
  Definition ex15_rec_xor:  << Bit, Unit >> ~> Bit :=
  <[ \ x => letrec s = delay (xor x s) in s ]>.
  Definition ex16_triple:  << <<Bit, Bit, Bit>>, Unit >> ~> Bit :=
  <[ \ triple => let '(x, y, z) = triple in x ]>.
  Definition ex17_constant_via_list:  << Unit >> ~> Vector (Vector Bit 4) 3 := <[  { 1, 2, 3 } ]>.

  Fixpoint copy_object_pow2 o (n:nat): Kind :=
  match n with
  | O => o
  | S n => Tuple (copy_object_pow2 o n) (copy_object_pow2 o n)
  end.

  Program Fixpoint tree
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

  Definition adder_tree
    (bitsize n: nat)
    : <<copy_object_pow2 (Vector Bit bitsize) n, Unit>> ~> (Vector Bit bitsize) :=
    tree (Vector Bit bitsize) n <[\x y => x +% y]>.

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

  Fixpoint reshape {n m A}
    :  << Vector A (n * m), Unit >> ~> << Vector (Vector A m) n >> :=
  match n with
  | 0 => <[\_ => [] ]>
  | S n' =>
    <[ \vec =>
      let '(x, xs) = split_at m vec in
      x :: !(@reshape n' m A) xs
      ]>
  end.

  Definition dummy {T}
    :  << Bit, T, T, Unit >> ~> <<T>> :=
    <[\_ x _ => x]>.
  Notation T:=(Bit )(only parsing).
  Notation "'if' i 'then' t 'else' e" :=
    (App (App (App (dummy _) i) t) e)
    (in custom expr at level 5, left associativity) : kappa_scope.
  Definition exfailed: << <<T,T>>,<<T,T>>, Unit >> ~> <<T,T>> :=
    <[\s1 s2 =>
    let '(a,b) : <<_,T>> =  s1 in
    let '(aa,bb) : <<_,_>> = s2 in
    if a then (a,b) else s1
    ]>.

End regression_examples.

