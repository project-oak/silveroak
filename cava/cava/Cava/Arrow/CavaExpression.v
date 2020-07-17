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

From Arrow Require Import Category Arrow Kappa ClosureConversion.
From Cava Require Import Arrow.CavaArrow.

From Coq Require Import Arith NArith Lia NaryFunctions.

Import EqNotations.

Open Scope category_scope.
Open Scope arrow_scope.

Section Vars.
  Context {var: Kind -> Kind -> Type}.

  Definition lift_constant (ty: Kind): Type :=
    match ty with
    | Bit => bool
    | Vector Bit n => N
    | _ => False
    end.

  (*
    `CavaExpr` includes constructors for
    - Kappa Calculus,
    - the Cava methods,
    - lifting any morphism from the Constructive arrow instance,
    - and miscellaneous methods

    The kappa calculus and LiftMorphism constructors are the only 5
    "primitive"/required constructors, the rest are a to help syntax
    or type inference and desugar simply to combinations of the others.
    *)
  (* TODO: cleanup / have a more modular EDSL representation *)
  Inductive CavaExpr : Kind -> Kind -> Type :=
    (* Kappa Calculus *)
    | Var: forall {x y},    var x y -> CavaExpr x y
    | Abs: forall {x y z},  (var Unit x -> CavaExpr y z) -> CavaExpr << x, y >> z
    | App: forall {x y z},  CavaExpr << x, y >> z -> CavaExpr Unit x -> CavaExpr y z
    | Com: forall {x y z},  CavaExpr y z -> CavaExpr x y -> CavaExpr x z

    (* Helper syntax *)
    | Let: forall {x y z},  CavaExpr Unit x -> (var Unit x -> CavaExpr y z) -> CavaExpr y z
    | Fst: forall {x y}, CavaExpr << << x, y >>, Unit >> x
    | Snd: forall {x y}, CavaExpr << << x, y >>, Unit >> y
    | Pair: forall {x y}, CavaExpr << x, y, Unit >> << x, y >>
    | Id: forall {x}, CavaExpr <<x, Unit>> x
    | Morphism: forall {i o}, (forall cava: Cava, i~[cava]~>o) -> CavaExpr i o

    (* Cava routines *)
    | LiftConstant: forall x, lift_constant x -> CavaExpr Unit x

    | Not: CavaExpr << Bit, Unit >> Bit
    | And: CavaExpr << Bit, Bit, Unit >> Bit
    | Nand: CavaExpr << Bit, Bit, Unit >> Bit
    | Or:   CavaExpr << Bit, Bit, Unit >> Bit
    | Nor:  CavaExpr << Bit, Bit, Unit >> Bit
    | Xor:  CavaExpr << Bit, Bit, Unit >> Bit
    | Xnor: CavaExpr << Bit, Bit, Unit >> Bit
    | Buf:  CavaExpr << Bit, Unit >>      Bit
    | Delay: forall {o}, CavaExpr << o, Unit >> o
    | Xorcy: CavaExpr << Bit, Bit, Unit >> Bit
    | Muxcy: CavaExpr << Bit, Tuple Bit Bit, Unit >> Bit
    | UnsignedAdd: forall a b c, CavaExpr << Vector Bit a, Vector Bit b, Unit >> (Vector Bit c)
    (* specialized adds *)
    | UnsignedAdd1: forall a b, CavaExpr << Vector Bit a, Vector Bit b, Unit >> (Vector Bit (max a b))
    | UnsignedAdd2: forall a b, CavaExpr << Vector Bit a, Vector Bit b, Unit >> (Vector Bit (1+max a b))

    | UnsignedSub: forall a, CavaExpr << Vector Bit a, Vector Bit a, Unit >> (Vector Bit a)

    | Lut n: (bool^^n --> bool) -> CavaExpr << Vector Bit n, Unit >> Bit

    | EmptyVec: forall {o}, CavaExpr Unit (Vector o 0)
    | Index: forall n {o}, CavaExpr << Vector o n, Vector Bit (Nat.log2_up n), Unit >> o
    | Cons: forall n {o}, CavaExpr << o, Vector o n, Unit >> (Vector o (S n))
    | Snoc: forall n {o}, CavaExpr << Vector o n, o, Unit >> (Vector o (S n))
    | Uncons: forall n {o}, CavaExpr << Vector o (S n), Unit >> << o, Vector o n >>
    | Unsnoc: forall n {o}, CavaExpr << Vector o (S n), Unit >> << Vector o n, o >>
    | Concat: forall n m {o}, CavaExpr << Vector o n, Vector o m, Unit >> (Vector o (n + m))
    | Split: forall n m {o}, CavaExpr << Vector o (n+m), Unit >> <<Vector o n, Vector o m>>
    | Slice: forall n x y {o}, x < n -> y <= x -> CavaExpr << Vector o n, Unit >> (Vector o (x - y + 1)) .

  Bind Scope kind_scope with CavaExpr.
  Delimit Scope kind_scope with CavaExpr.

  Arguments Kappa.Var [_ _ _ _ _ var _ _].
  Arguments Kappa.Abs [_ _ _ _ _ var _ _ _].
  Arguments Kappa.App [_ _ _ _ _ var _ _ _].
  Arguments Kappa.Comp [_ _ _ _ _ var _ _ _].
  Arguments Kappa.Morph [_ _ _ _ _ var _ _].
  Arguments Kappa.LetRec [_ _ _ _ _ var _ _ _].

  Definition liftCava `{Cava} i {o} (f: remove_rightmost_unit i ~> o)
    : kappa var i o :=
    Kappa.Comp (Kappa.Morph f) (Kappa.Morph (remove_rightmost_tt i)).

  Fixpoint desugar {cava: Cava} {i o} (e: CavaExpr i o) : kappa var i o :=
    match e with
    | Var x => Kappa.Var x
    | Abs f => Kappa.Abs (fun x => desugar (f x))
    | App e1 e2 => Kappa.App (desugar e1) (desugar e2)
    | Com f g => Kappa.Comp (desugar f) (desugar g)
    | Let x f => Kappa.App (Kappa.Abs (fun x => desugar (f x))) (desugar x)

    | Fst  => Kappa.Morph (cancelr >>> second drop >>> cancelr)
    | Snd  => Kappa.Morph (cancelr >>> first drop >>> cancell)

    | Pair => Kappa.Morph (second cancelr)

    | Id => liftCava <<_,u>> id

    | Not  => liftCava <<_,u>> not_gate
    | And  => liftCava <<_,_,u>> and_gate
    | Nand => liftCava <<_,_,u>> nand_gate
    | Or   => liftCava <<_,_,u>> or_gate
    | Nor  => liftCava <<_,_,u>> nor_gate
    | Xor  => liftCava <<_,_,u>> xor_gate
    | Xnor => liftCava <<_,_,u>> xnor_gate
    | Buf  => liftCava <<_,u>> buf_gate

    | Delay  => Kappa.Comp (Kappa.Morph delay_gate) (Kappa.Morph cancelr)

    | Xorcy  => liftCava <<_,_,u>> xorcy
    | Muxcy  => liftCava <<_,_,u>> muxcy
    | UnsignedAdd a b c => liftCava <<_,_,u>> (unsigned_add a b c)
    | UnsignedAdd1 a b => liftCava <<_,_,u>> (unsigned_add a b _)
    | UnsignedAdd2 a b => liftCava <<_,_,u>> (unsigned_add a b _)
    | UnsignedSub a => liftCava <<_,_,u>> (unsigned_sub a)
    | Lut n f => liftCava <<_,u>> (lut n f)

    | LiftConstant ty x =>
      match ty, x with
      | Bit, b => Kappa.Morph (constant b)
      | Vector Bit n, v => Kappa.Morph (constant_bitvec _ v)
      | _, H => match H with end
      end

    | Morphism m => Kappa.Morph (m _)

    | EmptyVec => liftCava <<u>> (empty_vec _)
    | Index n => liftCava <<_,_,u>> (index n _)
    | Cons n => liftCava <<_,_,u>> (cons n _)
    | Snoc n => liftCava <<_,_,u>> (snoc n _)
    | Uncons n => liftCava <<_,u>> (uncons n _)
    | Unsnoc n => liftCava <<_,u>> (unsnoc n _)
    | Concat n m => liftCava <<_,_,u>> (concat n m _)
    | Slice n x y H1 H2 => liftCava <<_,u>> (slice n x y _ H1 H2)
    | Split n m => liftCava <<_,u>> (split n m _)
    end.
End Vars.

Arguments CavaExpr : clear implicits.

Definition Desugar {_ :Cava} {i o} (e: forall var, CavaExpr var i o) : Kappa i o := fun var => desugar (e var).

Hint Resolve Desugar : core.
Hint Resolve desugar : core.
Hint Unfold Desugar : core.
Hint Unfold desugar : core.

Hint Extern 5 (NoLetRecKappa natvar _ _ (liftCava _ _)) =>
      apply NoLetRecComp; apply NoLetRecMorph : stateless.
Hint Extern 5 (MorphPropKappa natvar _ _ (liftCava _ _)) =>
      apply MorphPropComp : stateless.