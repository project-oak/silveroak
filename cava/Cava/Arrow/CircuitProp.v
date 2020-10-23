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

From Coq Require Import Bool ZArith NaryFunctions Vector.
From Cava Require Import Arrow.Classes.Category.
From Cava Require Import Arrow.Classes.Arrow.
From Cava Require Import Arrow.CircuitArrow Arrow.CircuitSemantics.
From Cava Require Import Arrow.ArrowKind Arrow.Primitives.
From Cava Require Import Arrow.ExprLowering.

From ExtLib Require Import Structures.Monoid.
Import VectorNotations.


Instance monoid_category m (M: Monoid m): Category Kind := {
  morphism _ _ := m;
  id _ := monoid_unit M;
  compose _ _ _ f g := monoid_plus M g f;
}.

Definition all_monoid : Monoid@{monoid_category.u0} bool := {|
  monoid_plus a b := a && b; monoid_unit := true
|}.

Instance monoid_arrow m (M: Monoid m) : Arrow Kind (monoid_category m M) Unit Tuple := {
  first _ _ _ f := f;
  second _ _ _ f := f;

  assoc   _ _ _ := monoid_unit M;
  unassoc _ _ _ := monoid_unit M;

  cancelr _ := monoid_unit M;
  cancell x := monoid_unit M;

  uncancell _ := monoid_unit M;
  uncancelr _ := monoid_unit M;
}.

Instance monoid_drop m (M: Monoid m): Arrows.Drop (monoid_arrow m M) :=
{ drop _ := monoid_unit M; }.
Instance monoid_copy m (M: Monoid m): Arrows.Copy (monoid_arrow m M) :=
{ copy _ := monoid_unit M; }.
Instance monoid_swap m (M: Monoid m): Arrows.Swap (monoid_arrow m M) :=
{ swap _ _ := monoid_unit M; }.

Instance monoid_rewrite_or_default m (M: Monoid m)
  : Arrows.RewriteOrDefault (monoid_arrow m M) := {
  rewrite_or_default _ _ := monoid_unit M;
}.

Instance ignore_annotation m (M: Monoid m) x: Arrows.Annotation (monoid_arrow m M) x := {
  annotate _ _ _ f := f
}.

Instance monoid_impossible m (M: Monoid m) : Arrows.Impossible (monoid_arrow m M) := {
  impossible _ _ := monoid_unit M;
}.

Instance monoid_loops m (M: Monoid m) : Arrows.Loop (monoid_arrow m M) := {
  loopl _ _ _ f := f;
  loopr _ _ _ f := f;
}.

Instance no_loops_loop : Arrows.Loop (monoid_arrow bool all_monoid) := {
  loopl _ _ _ _ := false;
  loopr _ _ _ _ := false;
}.

Instance all_primitives
  : Arrows.Primitive (monoid_arrow bool all_monoid)
    CircuitPrimitive primitive_input primitive_output := {
  primitive p := true;
}.

Instance no_delays_primitives
  : Arrows.Primitive (monoid_arrow bool all_monoid)
    CircuitPrimitive primitive_input primitive_output := {
  primitive p :=
    match p with
    | Delay _ => false
    | _ => true
    end;
}.

Set Typeclasses Unique Solutions.

Definition is_combinational {i o: Kind}
  (circuit: ExprSyntax.Kappa i o) :=
  (closure_conversion
    (arrow:=monoid_arrow bool all_monoid)
    (arrow_primitives:=no_delays_primitives)
    (arrow_loop:=no_loops_loop)
    circuit).

(* Ltac simply_combinational := *)
(*   vm_compute; reflexivity. *)

(* Local Open Scope category_scope. *)
(* Import CategoryNotations. *)

(* Lemma is_combinational_first: forall x y z (circuit: ExprSyntax.Kappa x y), *)
(*   is_combinational (first circuit : ExprSyntax.Kappa (x**z) (y**z)) = *)
(*   is_combinational circuit. *)
(* Proof. tauto. Qed. *)

(* Lemma is_combinational_second: forall x y z (circuit: x ~> y), *)
(*   is_combinational (second circuit : z**x ~> z**y) = *)
(*   is_combinational circuit. *)
(* Proof. tauto. Qed. *)

(* Section example. *)
(*   Definition ex_loopr {x y z: Kind} (c: x**z ~> y**z): x ~> y *)
(*     := loopr c. *)
(*   Definition ex_loopl {x y z: Kind} (c: z**x ~> z**y): x ~> y *)
(*     := loopl c. *)

(*   Example loopl_is_not_combinational : forall (x y z: Kind) (c: z**x ~> z**y), *)
(*     ~ is_combinational (ex_loopl c). *)
(*   Proof. vm_compute. intros. inversion x3. Qed. *)

(*   Example loopr_is_not_combinational : forall (x y z: Kind) (c: x**z ~> y**z), *)
(*     ~ is_combinational (ex_loopr c). *)
(*   Proof. vm_compute. intros. inversion x3. Qed. *)

  (* Example not_gate_is_combinational : *)
  (*   is_combinational (Primitive Not). *)
  (* Proof. *)

  (* simply_combinational. Qed. *)
(* End example. *)

