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

From Cava Require Import Arrow.Classes.Category.

Local Open Scope category_scope.

Reserved Infix "**" (at level 30, right associativity).

Generalizable All Variables .

Import CategoryNotations.

Class DecidableEquality T := {
  eq_dec: forall x y : T, {x = y} + {x <> y}
}.

(* generalized arrow *)
Class Arrow (object: Type) (category: Category object) (unit: object) (product: object -> object -> object) := {
  arrow_category := category;
  arrow_unit := unit;
  arrow_product := product
    where "x ** y" := (product x y);

  first  {x y z} (f: x ~> y) : x ** z ~> y ** z;
  second {x y z} (f: x ~> y) : z ** x ~> z ** y;

  bimap {x y z w} (f: x ~> y) (g: z ~> w) := first f >>> second g;

  assoc   {x y z} : ((x**y)**z) ~> (x**(y**z));
  unassoc {x y z} : (x**(y**z)) ~> ((x**y)**z);

  cancelr  {x} : x ** unit ~> x;
  cancell  {x} : unit ** x ~> x;

  uncancell {x} : x ~> unit**x;
  uncancelr {x} : x ~> x**unit;
}.

Coercion arrow_category: Arrow >-> Category.

Declare Scope arrow_scope.
Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (arrow_product x y)
  (at level 30, right associativity) : category_scope.

Class ArrowLaws
  (object: Set)
  (category: Category object) (category_laws: CategoryLaws category)
  (unit: object) (product: object -> object -> object) (A: Arrow object category unit product)
  := {
  (* (un)cance{l,r} and (un)assoc are natural isomorphisms *)
  first_cancelr   {x y} (f: x ~> y): first f >>> cancelr =M= cancelr >>> f;
  uncancelr_first {x y} (f: x ~> y): uncancelr >>> first f =M= f >>> uncancelr;

  second_cancell   {x y} (f: x ~> y): second f >>> cancell =M= cancell >>> f;
  uncancell_second {x y} (f: x ~> y): uncancell >>> second f =M= f >>> uncancell;

  assoc_iso {x y z w s t} (f: x ~> y) (g: z ~> w) (h: s ~> t):
    assoc >>> bimap _ _ _ _ f (bimap _ _ _ _ g h) =M= bimap _ _ _ _ (bimap _ _ _ _ f g) h >>> assoc;

  unassoc_iso {x y z w s t} (f: x ~> y) (g: z ~> w) (h: s ~> t):
    unassoc >>> bimap _ _ _ _ (bimap _ _ _ _ f g) h =M= bimap _ _ _ _ f (bimap _ _ _ _ g h) >>> unassoc;

  (* triangle and pentagon identities? *)
}.

Section with_continuation.
  Context `{arrow_laws: ArrowLaws}.

  Local Ltac prove_cont law :=
    rewrite <-associativity;
    setoid_rewrite law; apply associativity.

  Lemma first_cancelr_cont {x y z} (f: x ~> y) (k: _ ~> z):
    first f >>> cancelr >>> k =M= cancelr >>> f >>> k.
  Proof using arrow_laws. prove_cont (first_cancelr f). Qed.

  Lemma uncancelr_first_cont {x y z} (f: x ~> y) (k: _ ~> z):
    uncancelr >>> first f >>> k =M= f >>> uncancelr >>> k.
  Proof using arrow_laws. prove_cont (uncancelr_first f). Qed.

  Lemma second_cancell_cont {x y z} (f: x ~> y) (k: _ ~> z):
    second f >>> cancell >>> k =M= cancell >>> f >>> k.
  Proof using arrow_laws. prove_cont (second_cancell f). Qed.

  Lemma uncancell_second_cont {x y z} (f: x ~> y) (k: _ ~> z):
    uncancell >>> second f >>> k =M= f >>> uncancell >>> k.
  Proof using arrow_laws. prove_cont (uncancell_second f). Qed.

  Lemma assoc_iso_cont
        {x y z w s t v} (f: x ~> y) (g: z ~> w) (h: s ~> t) (k: _ ~> v):
    assoc >>> bimap _ _ _ _ f (bimap _ _ _ _ g h) >>> k
    =M= bimap _ _ _ _ (bimap _ _ _ _ f g) h >>> assoc >>> k.
  Proof using arrow_laws. prove_cont (assoc_iso f g h). Qed.

  Lemma unassoc_iso_cont
        {x y z w s t v} (f: x ~> y) (g: z ~> w) (h: s ~> t) (k: _ ~> v):
    unassoc >>> bimap _ _ _ _ (bimap _ _ _ _ f g) h >>> k
    =M= bimap _ _ _ _ f (bimap _ _ _ _ g h) >>> unassoc >>> k.
  Proof using arrow_laws. prove_cont (unassoc_iso f g h). Qed.
End with_continuation.

Inductive void := .

Lemma void_is_false: void -> False.
Proof.
  intros.
  destruct H.
Qed.

Module Arrows.
  Class Copy `(A: Arrow) := {
    copy {x} : x ~> x**x;
  }.

  Class Drop `(A: Arrow) := {
    drop {x} : x ~> arrow_unit;
  }.

  Class Swap `(A: Arrow) := {
    swap {x y} : x**y ~> y**x;
  }.

  Class Loop `(A: Arrow) := {
    loopr {x y z} : (x**z ~> y**z) -> (x ~> y);
    loopl {x y z} : (z**x ~> z**y) -> (x ~> y);
  }.

  Class Constant `(A: Arrow) t v := {
    constant : v -> (arrow_unit ~> t);
  }.

  Class RewriteOrDefault `(A: Arrow) := {
    rewrite_or_default : forall x y, x ~> y;
  }.

  Class RewriteOrDefaultLaw `(A: Arrow) := {
    rewrite_or_default_refl :
      forall x (r: RewriteOrDefault A),
      rewrite_or_default x x = id;
  }.

  Class Annotation `(A: Arrow) ann := {
    annotate : forall {x y}, ann -> (x ~> y) -> (x ~> y);
  }.

  Class Sum
    object (category: Category object)
    void either (ASum: Arrow object category void either)
    := {
    merge {x} : (either x x) ~> x;
    never {x} : void ~> x;
  }.

  (* A case that can never happen *)
  Class Impossible `(A: Arrow) := {
    impossible : forall {x y}, x ~> y;
  }.

  Class Primitive `(A: Arrow) primitive primitive_proj_i primitive_proj_o := {
    primitive (p: primitive) : primitive_proj_i p ~> primitive_proj_o p;
  }.
End Arrows.

