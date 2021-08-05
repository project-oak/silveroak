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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.

Require Import Cava.Types.
Require Import Cava.Primitives.

Local Open Scope N.

Definition tvar : Type := type -> Type.
Existing Class tvar.

Section Vars.
  Inductive Circuit {var: tvar}: type -> type -> type -> Type :=
  | Var : forall {x},     var x -> Circuit [] [] x
  | Abs : forall {s x y z}, (var x -> Circuit s y z) -> Circuit s (x ** y) z
  | App : forall {s1 s2 x y z}, Circuit s2 (x ** y) z -> Circuit s1 [] x -> Circuit (s1 ++ s2) y z

  | Let: forall {x y z s1 s2}, Circuit s1 [] x -> (var x -> Circuit s2 y z) -> Circuit (s1++s2) y z
  (* slightly different fomualtion, but equivalent to loop delay *)
  | LetDelay : forall {x y z s1 s2}, denote_type x
    -> (var x -> Circuit s1 [] x)
    -> (var x -> Circuit s2 y z)
    -> Circuit (x ++ s1 ++ s2) y z

  | Delay: forall {x}, denote_type x -> Circuit x [x] x

  | ElimBool: forall {s1 s2 x},
    Circuit [] [] Bit
    -> Circuit s1 [] x
    -> Circuit s2 [] x
    -> Circuit (s1++s2) [] x
  | ElimPair: forall {x y z s},
    (var x -> var y -> Circuit s [] z)
    -> var (x**y)
    -> Circuit s [] z

  | Constant: forall {x}, denote_type x -> Circuit [] [] x
  | MakePair: forall {s1 s2 x y}, Circuit s1 [] x
    -> Circuit s2 [] y
    -> Circuit (s1++s2) [] (x**y)

  | UnaryOp : forall {x r}, UnaryPrim x r -> var x -> Circuit [] [] r
  | BinaryOp : forall {x y r}, BinaryPrim x y r -> var x -> var y -> Circuit [] [] r
  | TernaryOp : forall {x y z r}, TernaryPrim x y z r -> var x -> var y -> var z -> Circuit [] [] r
  .
End Vars.

Declare Scope expr_scope.
Declare Custom Entry expr.
Delimit Scope expr_scope with expr.

Module ExprNotations.
  (* Escaping *)
  Notation "{{ x }}"   := (x)%expr (at level 1, x custom expr at level 99).
  Notation "` x `" := (x) (in custom expr at level 2, x constr at level 1) : expr_scope.

  Notation "f x"     := (App f x) (in custom expr at level 3, left associativity) : expr_scope.
  Notation "x"       := (Var x) (in custom expr, x ident) : expr_scope.
  Notation "( x )"   := (x)(in custom expr, x at level 1) : expr_scope.

  Notation "'fun' x .. y => e" := (
      Abs (fun x => .. (Abs (fun y => e)) ..)
    ) ( in custom expr at level 1
    , x binder, y binder, e custom expr at level 1) : expr_scope.

  Notation "'let' x := a 'in' e" := (
      Let a (fun x => e)
    ) ( in custom expr at level 1
    , x pattern at level 4, e at level 99, a at level 1) : expr_scope.

  Notation "'let' '( x , .. , y ; z ) := a 'in' e" := (
      Let a (ElimPair (fun x => ..  (ElimPair (fun y z => e)) .. ))
    ) ( in custom expr at level 1
    , x closed binder, y closed binder, z binder, a at level 1, e at level 99) : expr_scope.

  Notation "'let/delay' x := a 'initially' v 'in' e" := (
      LetDelay (v: denote_type _) (fun x => a) (fun x => e)
    ) ( in custom expr at level 1
    , x pattern at level 4, v constr at level 99, e at level 7, a at level 1) : expr_scope.

  Notation "'let/delay' '( x , .. , y ; z ) := a 'initially' v 'in' e" := (
      LetDelay v
      ( ElimPair (fun x => ..  (ElimPair (fun y z => a)) .. ) )
      ( ElimPair (fun x => ..  (ElimPair (fun y z => e)) .. ) )
    ) ( in custom expr at level 1
    , x closed binder, y closed binder, z binder, a at level 1, e at level 7, v constr ) : expr_scope.

  (* Ltac for better type inference on the initial value *)
  Notation "'delay' x 'initially' v" := (
    (ltac:(
      match type of x with
      | Circuit _ _ ?t =>
          exact (App (Delay (v : denote_type t)) (x : Circuit _ _ t))
      end
    ))
    )
    (in custom expr at level 1, x at level 4, v constr at level 7, only parsing)  : expr_scope.

  Notation "( x , .. , y , z )" := (
      MakePair x .. (MakePair y z) ..
    ) (in custom expr, x at level 1, y at level 1, z at level 1) : expr_scope.

  Notation "'if' i 'then' t 'else' e" := ((ElimBool i t e))
    (in custom expr at level 5, left associativity) : expr_scope.

End ExprNotations.

Section Var.
  Context {var : tvar}.

  Definition True := Constant (true: denote_type Bit).
  Definition False := Constant (false: denote_type Bit).
  Definition K {sz}: N -> Circuit [] [] (BitVec sz) :=
    fun x : denote_type (BitVec sz) => Constant x.

  Class bitlike x :=
  { eq : var x -> var x -> Circuit [] [] Bit
  ; not : var x -> Circuit [] [] x
  (* ; xor : var x -> var x -> Circuit [] [] x *)
  (* ; and : var x -> var x -> Circuit [] [] x *)
  (* ; add : var x -> var x -> Circuit [] [] x *)
  }.

  Import ExprNotations.
  Instance bit_bitlike: bitlike Bit :=
  { eq x y :=  {{ `BinaryOp BinEq x y` }}
  ; not x := {{ `UnaryOp UnNot x` }}
  }.
  Instance bitvec_bitlike n: bitlike (BitVec n) :=
  { eq x y :=  {{ `BinaryOp BinEq x y` }}
  ; not x := {{ `UnaryOp UnBitVecNot x` }}
  }.

End Var.

Existing Instance bit_bitlike.
Existing Instance bitvec_bitlike.

Section RegressionTests.
  Import ExprNotations.

  Context {var : tvar}.

  Definition fork2 {A} : Circuit [] [A] (A ** A) := {{
    fun a => ( a, a)
  }}.

  Definition silly_id {A} : Circuit [] [A] A := {{
    fun a => let '(x,y;z) := (a, `fork2` a) in z
  }}.

  Definition fst3 {A} : Circuit [] [A**A**A] A := {{
    fun xyz => let '(x,y;z) := xyz in x
  }}.

  Definition ite_test {A} : Circuit [] [Bit; A] A := {{
    fun flag a =>
      if `silly_id` flag then (a) else a
  }}.

  Definition inital_state {sz} := (0,1)%N : denote_type (BitVec sz ** BitVec sz).

  Definition test {sz: nat}: Circuit (BitVec 10**BitVec 10) [] (BitVec 10) := {{
    let/delay '(x;y) := (y,x) initially inital_state in y
  }}.

  Definition test2 {sz: nat}: Circuit (BitVec sz ** BitVec sz) [BitVec sz ** BitVec sz ] (BitVec sz) := {{
    fun xy =>
    let '(x ; y) := xy in
    let/delay '(z;w) :=
      let t := x in
      (w, z)
      initially inital_state in
      x
  }}.

  (* Function composition for single arg functions *)
  Definition compose {s1 s2 x y z} (f: Circuit s1 [x] y) (g: Circuit s2 [y] z)
    : Circuit (s1++s2) [x] z := {{
    fun x => `g` ( `f` x )
  }}.
  (* Notation "f >=> g" := (compose f g) (at level 61, right associativity) : expr_scope. *)

End RegressionTests.

Axiom value_hole : forall {t}, t.
Axiom circuit_hole : forall {t var}, Circuit (var:=var) [] [] t.

Module PrimitiveNotations.
  Notation "x && y" := (
    Let x (fun v1 => Let y (fun v2 => BinaryOp BinBitAnd v1 v2))
  ) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x || y" := (
    Let x (fun v1 => Let y (fun v2 =>
     BinaryOp BinBitOr v1 v2
  ))) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x >= y" := (
    Let x (fun v1 => Let y (fun v2 =>
    BinaryOp BinBitVecGte v1 v2
  ))) (in custom expr at level 19, no associativity) : expr_scope.

  Notation "! x" := (
    Let x not
  ) (in custom expr at level 20) : expr_scope.
  Notation "x == y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinEq v1 v2
  ))) (in custom expr at level 19, no associativity) : expr_scope.
  Notation "x ^ y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinBitVecXor v1 v2
  ))) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x & y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinBitVecAnd v1 v2
  ))) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x + y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinBitVecAddU v1 v2
  ))) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x - y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinBitVecSubU v1 v2
  ))) (in custom expr at level 20, left associativity) : expr_scope.
  Notation "x >>> y" := (
    Let x (fun v1 => UnaryOp (UnVecRotateRight y) v1
  )) (in custom expr at level 19, no associativity) : expr_scope.
  Notation "x >> y" := (
    Let x (fun v1 => UnaryOp (UnVecShiftRight y) v1
  )) (in custom expr at level 19, no associativity) : expr_scope.
  Notation "x <<+ y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinVecShiftInRight v1 v2
    ))) (in custom expr at level 19, no associativity) : expr_scope.
    Notation "x +>> y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinVecShiftInLeft v1 v2
    ))) (in custom expr at level 19, no associativity) : expr_scope.

  Notation "x :> y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinVecCons v1 v2
  ))) (in custom expr at level 19, right associativity) : expr_scope.

  Notation "x ++ y" := (
    Let x (fun v1 => Let y (fun v2 =>
      BinaryOp BinVecConcat v1 v2
  ))) (in custom expr at level 19, right associativity) : expr_scope.

  Notation "[ ]" := (Constant (simple_denote_to_denote (t:=Vec _ 0) nil)) (in custom expr at level 19) : expr_scope.

  Import ExprNotations.
  Definition index {var t n i}: Circuit (var:=var) [] [Vec t n; BitVec i] t :=
    {{ fun vec index => `BinaryOp BinVecIndex vec index` }}.
  Definition vec_as_tuple {var t n}: Circuit (var:=var) [] [Vec t (S n)] (ntuple t n) :=
    {{ fun vec => `UnaryOp UnVecToTuple vec` }}.
  Definition slice {var t n} (start length: nat): Circuit (var:=var) [] [Vec t n] (Vec t length) :=
    {{ fun vec => `UnaryOp (UnVecSlice start length) vec` }}.
  Definition replace {var t n i}: Circuit (var:=var) [] [Vec t n; BitVec i; t] (Vec t n) :=
    {{ fun vec index val => `TernaryOp TernVecReplace vec index val` }}.
  Definition resize {var t n m}: Circuit (var:=var) [] [Vec t n] (Vec t m) :=
    {{ fun vec => `UnaryOp UnVecResize vec ` }}.
  Definition reverse {var t n}: Circuit (var:=var) [] [Vec t n] (Vec t n) :=
    {{ fun vec => `UnaryOp UnVecReverse vec ` }}.

End PrimitiveNotations.
