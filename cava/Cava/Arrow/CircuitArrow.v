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

Require Import Coq.Lists.List.
Require Import Cava.Arrow.Classes.Category Cava.Arrow.Classes.Arrow.
Require Import Cava.Arrow.Primitives.

Import ListNotations.
Import CategoryNotations.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

Set Implicit Arguments.

Notation arrow_input x := (arrow_input (object:=Kind) (unit:=Unit) (product:=Tuple) x).
Notation arrow_output x := (arrow_output (object:=Kind) (unit:=Unit) (product:=Tuple) x).

Section x.
  (* Single clock circuit *)
  Inductive Circuit: Kind -> Kind -> Type :=
  | Structural: forall (x: ArrowStructure), Circuit (arrow_input x) (arrow_output x)
  | Primitive: forall (x: CircuitPrimitive), Circuit (primitive_input x) (primitive_output x)

  (* contains subcircuits *)
  | Composition: forall x y z, Circuit x y -> Circuit y z -> Circuit x z
  | First: forall x y z, Circuit x y -> Circuit (Tuple x z) (Tuple y z)
  | Second: forall x y z, Circuit x y -> Circuit (Tuple z x) (Tuple z y)
  | Loopr: forall x y z, Circuit (Tuple x z) (Tuple y z) -> Circuit x y
  | Loopl: forall x y z, Circuit (Tuple z x) (Tuple z y) -> Circuit x y

  | Delay: forall x, Circuit x x
  | RewriteTy: forall x y, Circuit x y
  | Call: forall x y, nat -> Circuit x y
  .

  Fixpoint renumber {i o} (fn: nat -> nat) (x: Circuit i o): Circuit i o :=
    match x with
    | Composition f g => Composition (renumber fn f) (renumber fn g)
    | First _ f => First _ (renumber fn f)
    | Second _ f => Second _ (renumber fn f)
    | Loopr f => Loopr (renumber fn f)
    | Loopl f => Loopl (renumber fn f)

    | Call _ _ n => Call _ _ (fn n)
    | x => x
    end.

  (* Fixpoint ident_max {i o} (x: Circuit i o): nat := *)
  (*   match x with *)
  (*   | Composition f g => max (ident_max f) (ident_max g) *)
  (*   | First _ f => ident_max f *)
  (*   | Second _ f => ident_max f *)
  (*   | Loopr f => ident_max f *)
  (*   | Loopl f => ident_max f *)
  (*   | Call _ _ n => n *)
  (*   | x => 0 *)
  (*   end. *)

  Record TopCircuit (i o : Kind) : Type := mkTop {
    fragments : list { '(i,o) & Circuit i o} ;
    toplevel : Circuit i o
  }.

  Definition renumber_top {i o} (fn: nat -> nat) (x: TopCircuit i o): TopCircuit i o :=
    match x with
    | mkTop frag top => mkTop (map (
      fun '(existT _ (x,y) c) => existT _ (x,y) (renumber fn c)
    ) frag) (renumber fn top)
    end.

End x.

Instance CircuitCat : Category Kind := {
  morphism X Y := Circuit X Y;
  id X := Structural (Id X);
  compose X Y Z f g := Composition g f;
}.

Instance CircuitArrow : Arrow Kind CircuitCat Unit Tuple := {
  first  _ _ f := First f;
  second _ _ f := Second f;
  assoc   x y z := Structural (Assoc x y z);
  unassoc x y z := Structural (Unassoc x y z);
  cancelr  x := Structural (Cancelr x);
  cancell  x := Structural (Cancell x);
  uncancell x := Structural (Uncancell x);
  uncancelr x := Structural (Uncancelr x);
}.

Instance CircuitArrowDrop : ArrowDrop CircuitArrow := { drop _ := Structural (Drop _); }.
Instance CircuitArrowSwap : ArrowSwap CircuitArrow := { swap _ _ := Structural (Swap _ _); }.
Instance CircuitArrowCopy : ArrowCopy CircuitArrow := { copy _ := Structural (Copy _); }.
Instance CircuitArrowLoop : ArrowLoop CircuitArrow := { loopl := Loopl; loopr := Loopr; }.
Instance CircuitArrowSTKC : ArrowSTKC CircuitArrow := { }.

(* Definition high : Unit ~> Bit := Primitive (P0 (Constant Bit true)). *)
(* Definition low : Unit ~> Bit := Primitive (P0 (Constant Bit false)). *)
