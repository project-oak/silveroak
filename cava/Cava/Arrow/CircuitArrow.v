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

From Coq Require Import Lists.List NaryFunctions String Arith NArith Vector Lia.

Import ListNotations.
Import VectorNotations.

From Cava Require Import Arrow.Classes.Category Arrow.Classes.Arrow.
From Cava Require Import Arrow.ArrowKind.
From Cava Require Import Arrow.Primitives.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

(* Class CircuitLaws `(A: Arrow, ! ArrowCopy A, ! ArrowSwap A, ! ArrowDrop A) := {
  cancelr_unit_uncancelr {x}: @cancelr x >>> uncancelr =M= id;
  cancell_unit_uncancell {x}: @cancell _ _ A x >>> uncancell =M= id;
  uncancelr_cancelr {x}:      @uncancelr _ _ A x >>> cancelr =M= id;
  uncancell_cancell {x}:      @uncancell _ _ A x >>> cancell =M= id;

  drop_annhilates {x y} (f: x~>y): f >>> drop =M= drop;

  cancelr_unit_is_drop : @cancelr A unit =M= drop;
  cancell_unit_is_drop : @cancell A unit =M= drop;

  first_first   {x y z w} (f: x~>y) (g:y~>z): @first A x y w f >>> first g  =M= first (f >>> g);
  second_second {x y z w} (f: x~>y) (g:y~>z): @second A x y w f >>> second g  =M= second (f >>> g);

  swap_swap {x y}: @swap A _ x y >>> swap =M= id;

  first_id  {x w}: @first A x x w id  =M= id;
  second_id {x w}: @second A x x w id  =M= id;

  first_f  {x y w} (f: x~>y) (g:x~>y): f =M= g -> @first A x y w f =M= first g;
  second_f {x y w} (f: x~>y) (g:x~>y): f =M= g -> @second A x y w f =M= second g;
}. *)

Notation arrow_input x := (arrow_input (object:=Kind) (unit:=Unit) (product:=Tuple) x).
Notation arrow_output x := (arrow_output (object:=Kind) (unit:=Unit) (product:=Tuple) x).

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

  | RewriteTy: forall x y, Circuit x y
  .

Instance CircuitCat : Category Kind := {
  morphism X Y := Circuit X Y;
  id X := Structural (Id X);
  compose X Y Z f g := Composition X Y Z g f;
}.

Instance CircuitArrow : Arrow Kind CircuitCat Unit Tuple := {
  first  f := First f;
  second f := Second f;
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

Ltac match_primitive X :=
  match X with
  | (Circuit _ _ _) => idtac
  end.

Ltac match_compose X :=
  match X with
  | (Composition _ _ ?Y ?Z) => idtac
  end.

Definition high : Unit ~> Bit := Primitive (Constant Bit true).
Definition low : Unit ~> Bit := Primitive (Constant Bit false).
