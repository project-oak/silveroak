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
Require Import coqutil.Tactics.Tactics.
From Cava Require Import Arrow.Classes.Category.
From Cava Require Import Arrow.Classes.Arrow.
From Cava Require Import Arrow.CircuitArrow Arrow.CircuitSemantics.
From Cava Require Import Arrow.ArrowKind Arrow.Primitives.
From Cava Require Import Arrow.ExprSyntax.
From Cava Require Import Arrow.ExprLowering.
From Cava Require Import Arrow.ExprLoweringPreservation.
From Cava Require Import Arrow.ExprEquiv.
From Cava Require Import Arrow.ExprSemantics.

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
    (arrow_rewrite_or_default:=monoid_rewrite_or_default _ _)
    (arrow_annotation:=ignore_annotation _ _ _)
    (arrow_impossible:=monoid_impossible _ _)
    (arrow_drop:=monoid_drop _ _)
    (arrow_copy:=monoid_copy _ _)
    (arrow_swap:=monoid_swap _ _)
    circuit).

(* TODO(blaxill): this should be true *)
Lemma is_combinational_true_no_letrec {i o: Kind}:
  forall e: Kappa i o, NoLetRec e -> is_combinational e = true.
Abort.

