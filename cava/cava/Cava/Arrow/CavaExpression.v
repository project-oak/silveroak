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
    `kappa_sugared` includes constructors for
    - Kappa Calculus,
    - the Cava methods,
    - lifting any morphism from the Constructive arrow instance,
    - and miscellaneous methods

    The kappa calculus and LiftMorphism constructors are the only 5
    "primitive"/required constructors, the rest are a to help syntax
    or type inference and desugar simply to combinations of the others.
    *)
  (* TODO: cleanup / have a more modular EDSL representation *)
  Inductive kappa_sugared : Kind -> Kind -> Type :=
    (* Kappa Calculus *)
    | Var: forall {x y},    var x y -> kappa_sugared x y
    | Abs: forall {x y z},  (var Unit x -> kappa_sugared y z) -> kappa_sugared << x, y >> z
    | App: forall {x y z},  kappa_sugared << x, y >> z -> kappa_sugared Unit x -> kappa_sugared y z
    | Com: forall {x y z},  kappa_sugared y z -> kappa_sugared x y -> kappa_sugared x z

    (* Helper syntax *)
    | Let: forall {x y z},  kappa_sugared Unit x -> (var Unit x -> kappa_sugared y z) -> kappa_sugared y z
    | Fst: forall {x y}, kappa_sugared << << x, y >>, Unit >> x
    | Snd: forall {x y}, kappa_sugared << << x, y >>, Unit >> y
    | Pair: forall {x y}, kappa_sugared << x, y, Unit >> << x, y >>

    (* Cava routines *)
    | LiftConstant: forall {x}, lift_constant x -> kappa_sugared Unit x

    | Not: kappa_sugared << Bit, Unit >> Bit
    | And: kappa_sugared << Bit, Bit, Unit >> Bit
    | Nand: kappa_sugared << Bit, Bit, Unit >> Bit
    | Or:   kappa_sugared << Bit, Bit, Unit >> Bit
    | Nor:  kappa_sugared << Bit, Bit, Unit >> Bit
    | Xor:  kappa_sugared << Bit, Bit, Unit >> Bit
    | Xnor: kappa_sugared << Bit, Bit, Unit >> Bit
    | Buf:  kappa_sugared << Bit, Unit >>      Bit
    | Delay: forall {o}, kappa_sugared << o, Unit >> o
    | Xorcy: kappa_sugared << Bit, Bit, Unit >> Bit
    | Muxcy: kappa_sugared << Bit, Tuple Bit Bit, Unit >> Bit
    | UnsignedAdd: forall a b c, kappa_sugared << Vector Bit a, Vector Bit b, Unit >> (Vector Bit c)

    | Lut n: (bool^^n --> bool) -> kappa_sugared << Vector Bit n, Unit >> Bit

    | EmptyVec: forall {o}, kappa_sugared Unit (Vector o 0)
    | Index: forall n {o}, kappa_sugared << Vector o n, Vector Bit (Nat.log2_up n), Unit >> o
    | Cons: forall n {o}, kappa_sugared << o, Vector o n, Unit >> (Vector o (S n))
    | Snoc: forall n {o}, kappa_sugared << Vector o n, o, Unit >> (Vector o (S n))
    | Uncons: forall n {o}, kappa_sugared << Vector o (S n), Unit >> << o, Vector o n >>
    | Unsnoc: forall n {o}, kappa_sugared << Vector o (S n), Unit >> << Vector o n, o >>
    | Concat: forall n m {o}, kappa_sugared << Vector o n, Vector o m, Unit >> (Vector o (n + m))
    | Split: forall n m {o}, (m <= n) -> kappa_sugared << Vector o n, Unit >> <<Vector o m, Vector o (n - m)>>
    | Slice: forall n x y {o}, x < n -> y <= x -> kappa_sugared << Vector o n, Unit >> (Vector o (x - y + 1)) .

  Bind Scope kind_scope with kappa_sugared.
  Delimit Scope kind_scope with kappa_sugared.

  Definition tupleHelper {X Y}
    (x: kappa_sugared Unit X)
    (y: kappa_sugared Unit Y) :=
    App (App Pair x) y.

  Arguments Kappa.Var [_ _ _ _ _ var _ _].
  Arguments Kappa.Abs [_ _ _ _ _ var _ _ _].
  Arguments Kappa.App [_ _ _ _ _ var _ _ _].
  Arguments Kappa.Comp [_ _ _ _ _ var _ _ _].
  Arguments Kappa.Morph [_ _ _ _ _ var _ _].
  Arguments Kappa.LetRec [_ _ _ _ _ var _ _ _].

  Definition liftCava `{Cava} i {o} (f: remove_rightmost_unit i ~> o) 
    : kappa var i o :=
    Kappa.Comp (Kappa.Morph f) (Kappa.Morph (remove_rightmost_tt i)).

  Fixpoint desugar {cava: Cava} {i o} (e: kappa_sugared i o) : kappa var i o :=
    match e with
    | Var x => Kappa.Var x
    | Abs f => Kappa.Abs (fun x => desugar (f x))
    | App e1 e2 => Kappa.App (desugar e1) (desugar e2)
    | Com f g => Kappa.Comp (desugar f) (desugar g)
    | Let x f => Kappa.App (Kappa.Abs (fun x => desugar (f x))) (desugar x)

    | Fst  => Kappa.Morph (cancelr >>> second drop >>> cancelr)
    | Snd  => Kappa.Morph (cancelr >>> first drop >>> cancell)

    | Pair => Kappa.Morph (second cancelr)

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
    | Lut n f => liftCava <<_,u>> (lut n f)

    | @LiftConstant ty x =>
      match ty, x with
      | Bit, b => Kappa.Morph (constant b)
      | Vector Bit n, v => Kappa.Morph (constant_bitvec _ v)
      | _, H => match H with end
      end

    | EmptyVec => liftCava <<u>> (empty_vec _)
    | Index n => liftCava <<_,_,u>> (index n _)
    | Cons n => liftCava <<_,_,u>> (cons n _)
    | Snoc n => liftCava <<_,_,u>> (snoc n _)
    | Uncons n => liftCava <<_,u>> (uncons n _)
    | Unsnoc n => liftCava <<_,u>> (unsnoc n _)
    | Concat n m => liftCava <<_,_,u>> (concat n m _)
    | Slice n x y H1 H2 => liftCava <<_,u>> (slice n x y _ H1 H2)
    | Split n m H => liftCava <<_,u>> (split n m _ H)
    end.
End Vars.

Arguments kappa_sugared : clear implicits.

Definition Kappa_sugared i o := forall var, kappa_sugared var i o.

Definition Desugar `{Cava} {i o} (e: Kappa_sugared i o) : Kappa i o := fun var => desugar (e var).

Hint Resolve Desugar : core.
Hint Resolve desugar : core.
