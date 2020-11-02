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

From Coq Require Import Arith.Arith Logic.Eqdep_dec Lists.List micromega.Lia
     NArith.NArith Strings.String.
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

Set Implicit Arguments.
Generalizable All Variables.

(* Kappa expression and application *)

Inductive NotationExpr: Kind -> Kind -> Type :=
| ModuleExpr : forall x y, Module (Kappa x y) -> NotationExpr x y
| FragmentExpr : forall x y, Kappa x y -> NotationExpr x y.

Definition instantiate {x y var} (e: NotationExpr x y) : kappa var x y :=
  match e with
  | ModuleExpr e => CallModule (module_instantiate_var e)
  | FragmentExpr e => e var
  end.

Class instantiatable_expr (expr: Type) x y := {
  embed_expr : expr -> NotationExpr x y
}.

Instance instantiatable_module x y : instantiatable_expr (Module (Kappa x y)) x y := {
  embed_expr module := ModuleExpr module;
}.

Instance instantiatable_fragment x y : instantiatable_expr (Kappa x y) x y := {
  embed_expr e := FragmentExpr e;
}.

Instance instantiatable_embedded x y : instantiatable_expr (NotationExpr x y) x y := {
  embed_expr e := e;
}.

Definition kappa_to_expr {x y} (e: Module (Kappa x y)) := ModuleExpr e.
Definition frag_to_expr {x y} (e: Kappa x y) := FragmentExpr e.

Coercion kappa_to_expr: Module >-> NotationExpr.
Coercion frag_to_expr: Kappa >-> NotationExpr.

Module KappaNotation.

  Notation "<[ e ]>" := (
    mkModule (fun var => e%kappa)
   ) (at level 1, e custom expr at level 1).

  Notation "<{ e }>" := (
    (fun var => e%kappa):Kappa _ _
   ) (at level 1, e custom expr at level 1).

  Notation "x ~> y" := (NotationExpr x y).

  Notation Fragment x y := (Kappa x y).
  Notation Module x y := (Module (Kappa x y)).

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
    | Tuple l r => P1 (Fst l r)
    | _ => P1 (Fst Unit Unit)
    end.

  Notation "'let' '( x , y ) = a 'in' b" := (
    Let a (fun a_binder =>
    Let (App (Primitive (P1 (Fst _ _))) (Var a_binder)) (fun x =>
      Let (App (Primitive (P1 (Snd _ _))) (Var a_binder)) (fun y => b))))
    ( in custom expr at level 1, x constr, y constr, b at level 7) : kappa_scope.

  Notation "'let' '( x , y ) : ty = a 'in' b" := (
    Let a (fun a_binder =>
    Let (App (Primitive (proj1_tuple1 ty)) (Var a_binder)) (fun x =>
      Let (App (Primitive (P1 (Snd _ _ ))) (Var a_binder)) (fun y => b))))
    ( in custom expr at level 1, x constr, y constr, ty constr at level 7, b at level 7) : kappa_scope.

  Notation "'let' '( x , y , z ) = a 'in' b" := (
    Let a (fun a_binder =>
    Let (App (Primitive (P1 (Fst _ _ ))) (Var a_binder)) (fun x =>
      Let (App (Primitive (P1 (Snd _ _ ))) (Var a_binder)) (fun a_tl_binder =>
        Let (App (Primitive (P1 (Fst _ _ ))) (Var a_tl_binder)) (fun y =>
          Let (App (Primitive (P1 (Snd _ _ ))) (Var a_tl_binder)) (fun z =>
          b))))))
    ( in custom expr at level 1, x constr, y constr, z constr, b at level 7) : kappa_scope.
  Notation "'let' '( x , y , z , w ) = a 'in' b" := (
    Let a (fun a_binder =>
    Let (App (Primitive (P1 (Fst _ _ ))) (Var a_binder)) (fun x =>
      Let (App (Primitive (P1 (Snd _ _ ))) (Var a_binder)) (fun a_tl_binder =>
        Let (App (Primitive (P1 (Fst _ _ ))) (Var a_tl_binder)) (fun y =>
            Let (App (Primitive (P1 (Snd _ _ ))) (Var a_tl_binder)) (fun a_tl_tl_binder =>
              Let (App (Primitive (P1 (Fst _ _ ))) (Var a_tl_tl_binder)) (fun z =>
                Let (App (Primitive (P1 (Snd _ _ ))) (Var a_tl_tl_binder)) (fun w =>
          b))))))))
    ( in custom expr at level 1, x constr, y constr, z constr, w constr, b at level 7) : kappa_scope.
  Notation "'let' '( x1 , x2 , x3 , x4 , x5 ) = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (P1 (Fst _ _ ))) (Var binder1)) (fun x1 =>
      Let (App (Primitive (P1 (Snd _ _ ))) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (P1 (Fst _ _ ))) (Var binder2)) (fun x2 =>
            Let (App (Primitive (P1 (Snd _ _ ))) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (P1 (Fst _ _ ))) (Var binder3)) (fun x3 =>
                Let (App (Primitive (P1 (Snd _ _ ))) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (P1 (Fst _ _ ))) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (P1 (Snd _ _ ))) (Var binder4)) (fun x5 =>
          b))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr
    , b at level 7) : kappa_scope.
  Notation "'let' '( x1 , x2 , x3 , x4 , x5 , x6 ) = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (P1 (Fst _ _ ))) (Var binder1)) (fun x1 =>
      Let (App (Primitive (P1 (Snd _ _ ))) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (P1 (Fst _ _ ))) (Var binder2)) (fun x2 =>
            Let (App (Primitive (P1 (Snd _ _ ))) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (P1 (Fst _ _ ))) (Var binder3)) (fun x3 =>
                Let (App (Primitive (P1 (Snd _ _ ))) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (P1 (Fst _ _ ))) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (P1 (Snd _ _ ))) (Var binder4)) (fun binder5 =>
                      Let (App (Primitive (P1 (Fst _ _ ))) (Var binder5)) (fun x5 =>
                        Let (App (Primitive (P1 (Snd _ _ ))) (Var binder5)) (fun x6 =>
          b))))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr, x6 constr
    , b at level 7) : kappa_scope.
  Notation "'let' '( x1 , x2 , x3 , x4 , x5 , x6 , x7 ) = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (P1 (Fst _ _ ))) (Var binder1)) (fun x1 =>
      Let (App (Primitive (P1 (Snd _ _ ))) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (P1 (Fst _ _ ))) (Var binder2)) (fun x2 =>
            Let (App (Primitive (P1 (Snd _ _ ))) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (P1 (Fst _ _ ))) (Var binder3)) (fun x3 =>
                Let (App (Primitive (P1 (Snd _ _ ))) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (P1 (Fst _ _ ))) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (P1 (Snd _ _ ))) (Var binder4)) (fun binder5 =>
                      Let (App (Primitive (P1 (Fst _ _ ))) (Var binder5)) (fun x5 =>
                        Let (App (Primitive (P1 (Snd _ _ ))) (Var binder5)) (fun binder6 =>
                            Let (App (Primitive (P1 (Fst _ _ ))) (Var binder6)) (fun x6 =>
                              Let (App (Primitive (P1 (Snd _ _ ))) (Var binder6)) (fun x7 =>
          b))))))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr, x6 constr, x7 constr
    , b at level 7) : kappa_scope.

  Notation "'let' '( x1 , x2 , x3 , x4 , x5 , x6 , x7 ) : ty = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (proj1_tuple1 ty)) (Var binder1)) (fun x1 =>
      Let (App (Primitive (P1 (Snd _ _ ))) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (P1 (Fst _ _ ))) (Var binder2)) (fun x2 =>
            Let (App (Primitive (P1 (Snd _ _ ))) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (P1 (Fst _ _ ))) (Var binder3)) (fun x3 =>
                Let (App (Primitive (P1 (Snd _ _ ))) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (P1 (Fst _ _ ))) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (P1 (Snd _ _ ))) (Var binder4)) (fun binder5 =>
                      Let (App (Primitive (P1 (Fst _ _ ))) (Var binder5)) (fun x5 =>
                        Let (App (Primitive (P1 (Snd _ _ ))) (Var binder5)) (fun binder6 =>
                            Let (App (Primitive (P1 (Fst _ _ ))) (Var binder6)) (fun x6 =>
                              Let (App (Primitive (P1 (Snd _ _ ))) (Var binder6)) (fun x7 =>
          b))))))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr, x6 constr, x7 constr
    , ty constr at level 7
    , b at level 7) : kappa_scope.

  Notation "'let' '( x1 , x2 , x3 , x4 , x5 , x6 , x7 , x8 ) : ty = a 'in' b" := (
    Let a (fun binder1 =>
    Let (App (Primitive (proj1_tuple1 ty)) (Var binder1)) (fun x1 =>
      Let (App (Primitive (P1 (Snd _ _ ))) (Var binder1)) (fun binder2 =>
        Let (App (Primitive (P1 (Fst _ _ ))) (Var binder2)) (fun x2 =>
            Let (App (Primitive (P1 (Snd _ _ ))) (Var binder2)) (fun binder3 =>
              Let (App (Primitive (P1 (Fst _ _ ))) (Var binder3)) (fun x3 =>
                Let (App (Primitive (P1 (Snd _ _ ))) (Var binder3)) (fun binder4 =>
                  Let (App (Primitive (P1 (Fst _ _ ))) (Var binder4)) (fun x4 =>
                    Let (App (Primitive (P1 (Snd _ _ ))) (Var binder4)) (fun binder5 =>
                      Let (App (Primitive (P1 (Fst _ _ ))) (Var binder5)) (fun x5 =>
                        Let (App (Primitive (P1 (Snd _ _ ))) (Var binder5)) (fun binder6 =>
                            Let (App (Primitive (P1 (Fst _ _ ))) (Var binder6)) (fun x6 =>
                              Let (App (Primitive (P1 (Snd _ _ ))) (Var binder6)) (fun binder7 =>
                                  Let (App (Primitive (P1 (Fst _ _ ))) (Var binder7)) (fun x7 =>
                                    Let (App (Primitive (P1 (Snd _ _ ))) (Var binder7)) (fun x8 =>
          b))))))))))))))))
    ( in custom expr at level 1
    , x1 constr, x2 constr, x3 constr, x4 constr, x5 constr, x6 constr, x7 constr, x8 constr
    , ty constr at level 7
    , b at level 7) : kappa_scope.

  (* Escaping *)

  Notation "! x" := ((instantiate (embed_expr x)) )(in custom expr at level 2, x global) : kappa_scope.
  Notation "!( x )" := ((instantiate (embed_expr x)) ) (in custom expr, x constr) : kappa_scope.

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

Import KappaNotation.
Local Open Scope kind_scope.

Section regression_examples.
  Import KappaNotation.
  Local Open Scope kappa_scope.

  Program Definition ex0_constant: Module << Vector Bit 10, Unit >> (Vector Bit 8)
    := <[ \x => x [: 7 : 0 ] ]>.

  Definition ex1_constant: Fragment << Bit, Unit >> Bit := <{ \x => true' }>.
  Definition ex2_parameterized (n: nat): Fragment << Bit, Unit >> Bit :=
  match n with
  | O => <{ \ x => true' }>
  | S n => <{ \ x => xor x x }>
  end.

  Definition ex3_to_vec: Module << Bit, Unit >> (Vector Bit 1) :=
  <[ \ x => x :: [] ]>.
  Definition ex4_index_vec:  Module << Vector Bit 10, Unit >> Bit :=
  <[ \ x => index x (# 1) ]>.
  Definition ex5_index_vec2:  Module << Vector Bit 10, Unit >> Bit :=
  <[ \ x => x [# 1] ]>.
  Definition ex6_concat:  Module << Vector Bit 2, Bit, Unit >> (Vector Bit 3) :=
  <[ \ x v => snoc x v ]>.
  Definition ex7_xor:  Module << Bit, Bit, Unit >> Bit :=
  <[ \ x y => xor x y ]>.
  Definition ex7_tupled_destruct:  Module << << Bit, Bit>>, Unit>> Bit :=
  <[ \ xy =>
    let '(x,y) : <<Bit,Bit>> = xy in
    y ]>.
  Definition ex8_multiindex:  Module << Vector (Vector Bit 5) 10, Unit >> Bit :=
  <[ \ x => x[#0][#1] ]>.
  Definition ex9_mkvec:  Module << Bit, Unit >> (Vector Bit 2) :=
  <[ \x => true' :: false' :: [] ]>.
  Definition ex10:  Module << Vector Bit 10, Vector Bit 10, Unit >> (Vector Bit 11) :=
  <[ \ x y => x + y ]>.
  Definition ex11:  Module << Vector Bit 10, Vector Bit 10, Unit >> (Vector Bit 10) :=
  <[ \ x y => x +% y ]>.
  Definition ex13:  Module << Vector Bit 10, Unit >> Bit :=
  <[ \ x => (xor x[#0] x[#1] :: false' :: []) [#0] ]>.
  Definition ex14:  Module << Vector Bit 10, Vector Bit 4, Unit >> Bit :=
  <[ \ x i => x [ i ] ]>.
  Definition ex15_rec_xor:  Module << Bit, Unit >> Bit :=
  <[ \ x => letrec s = delay (xor x s) in s ]>.
  Definition ex16_triple:  Module << <<Bit, Bit, Bit>>, Unit >> Bit :=
  <[ \ triple => let '(x, y, z) = triple in x ]>.
  Definition ex17_constant_via_list: Module << Unit >> (Vector (Vector Bit 4) 3) := <[  { 1, 2, 3 } ]>.

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
    : Fragment << copy_object_pow2 A n, Unit >> A :=
  match n with
  | O =>
    <{ \ x => x }>
  | S n' =>
    <{\ x =>
        let a = !(tree n' f) (fst x) in
        let b = !(tree n' f) (snd x) in
        !f a b
    }>
  end.

  Program Definition adder_tree
    (bitsize n: nat)
    : Module <<copy_object_pow2 (Vector Bit bitsize) n, Unit>> (Vector Bit bitsize) :=
    <[ !(tree n <{\x y => x +% y}> ) ]>.

  Definition xilinxFullAdder
    : Module << Bit, << Bit, Bit >>, Unit>> (Tuple Bit Bit) :=
    <[ \ cin ab =>
      let a = fst ab in
      let b = snd ab in
      let part_sum = xor a b in
      let sum      = xorcy part_sum cin in
      let cout     = muxcy part_sum (cin, a) in
      (sum, cout)
    ]>.

  Fixpoint reshape {n m A}
    : Fragment << Vector A (n * m), Unit >> << Vector (Vector A m) n >> :=
  match n with
  | 0 => <{\_ => [] }>
  | S n' =>
    <{ \vec =>
      let '(x, xs) = split_at m vec in
      x :: !(@reshape n' m A) xs
      }>
  end.

  Definition dummy {T}
    : Module << Bit, T, T, Unit >> <<T>> :=
    <[\_ x _ => x]>.
  Notation T:=(Bit )(only parsing).
  Notation "'if' i 'then' t 'else' e" :=
    (App (App (App (instantiate dummy) i) t) e)
    (in custom expr at level 5, left associativity) : kappa_scope.

  Definition exfailed: Module << <<T,T>>,<<T,T>>, Unit >> <<T,T>> :=
    <[\s1 s2 =>
    let '(a,b) : <<_,T>> =  s1 in
    let '(aa,bb) : <<_,_>> = s2 in
    if a then (a,b) else s1
    ]>.

End regression_examples.

