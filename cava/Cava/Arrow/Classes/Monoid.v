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

From Coq Require Import Bool.Bool.
From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Monoid.
From Cava Require Import Arrow.Classes.Category Arrow.Classes.Arrow.

Instance monoid_category k m (M: Monoid m): Category k := {
  morphism _ _ := m;
  id _ := monoid_unit M;
  compose _ _ _ f g := monoid_plus M g f;
}.

Definition all_monoid : Monoid@{monoid_category.u0} bool := {|
  monoid_plus a b := a && b; monoid_unit := true
|}.

Instance monoid_arrow k m (M: Monoid m) u t: Arrow k (monoid_category k m M) u t := {
  first _ _ _ f := f;
  second _ _ _ f := f;

  assoc   _ _ _ := monoid_unit M;
  unassoc _ _ _ := monoid_unit M;

  cancelr _ := monoid_unit M;
  cancell x := monoid_unit M;

  uncancell _ := monoid_unit M;
  uncancelr _ := monoid_unit M;
}.

Instance monoid_drop k m (M: Monoid m) u t: Arrows.Drop (monoid_arrow k m M u t) :=
{ drop _ := monoid_unit M; }.
Instance monoid_copy k m (M: Monoid m) u t: Arrows.Copy (monoid_arrow k m M u t) :=
{ copy _ := monoid_unit M; }.
Instance monoid_swap k m (M: Monoid m) u t: Arrows.Swap (monoid_arrow k m M u t) :=
{ swap _ _ := monoid_unit M; }.

Instance monoid_rewrite_or_default k m (M: Monoid m) u t
  : Arrows.RewriteOrDefault (monoid_arrow k m M u t) := {
  rewrite_or_default _ _ := monoid_unit M;
}.

Instance monoid_annotation k m (M: Monoid m) u t x: Arrows.Annotation (monoid_arrow k m M u t) x := {
  annotate _ _ _ f := f
}.

Instance monoid_impossible k m (M: Monoid m) u t: Arrows.Impossible (monoid_arrow k m M u t) := {
  impossible _ _ := monoid_unit M;
}.

Instance monoid_loops k m (M: Monoid m) u t: Arrows.Loop (monoid_arrow k m M u t) := {
  loopl _ _ _ f := f;
  loopr _ _ _ f := f;
}.

