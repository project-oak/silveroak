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

From ExtLib Require Import Structures.Monads.
From Cava Require Import Arrow.Classes.Category Arrow.Classes.Arrow.

Import MonadNotation.
Import CategoryNotations.
Local Open Scope monad_scope.

Definition build_denoted_category T denote : Category T :=
{|
  morphism X Y := denote X -> denote Y;
  id X a := a;
  compose X Y Z f g a := f (g a);
|}.

Program Definition build_denoted_arrow T denote unit tuple
  (tt: denote unit)
  (pair: forall {x y}, denote x -> denote y -> denote (tuple x y))
  (fst: forall {x y}, denote (tuple x y) -> denote x)
  (snd: forall {x y}, denote (tuple x y) -> denote y)
  : Arrow T (build_denoted_category T denote) unit tuple :=
{|
  first  x y z f := fun a : denote _ => pair (f (fst a)) (snd a);
  second x y z f := fun a => pair (fst a) (f (snd a));

  assoc   x y z := fun a => pair (fst (fst a)) (pair (snd (fst a)) (snd a));
  unassoc x y z := fun a => pair (pair (fst a) (fst (snd a))) (snd (snd a));

  cancelr x := fun a => fst a;
  cancell x := fun a => snd a;

  uncancell x := fun a => pair tt a;
  uncancelr x := fun a => pair a tt;
|}.

Instance coq_category : Category Type := {
  morphism X Y := X -> Y;
  id X a := a;
  compose X Y Z f g a := f (g a);
}.

Instance coq_arrow : Arrow Type coq_category unit prod := {
  first  x y z (f: x ~> y) a := (f (fst a), snd a);
  second x y z (f: x ~> y) a := (fst a, f (snd a));

  assoc   x y z a := (fst (fst a), (snd (fst a), snd a));
  unassoc x y z a := ((fst a, fst (snd a)), snd (snd a));

  cancelr x a := (fst a);
  cancell x a := (snd a);

  uncancell x a := (tt, a);
  uncancelr x a := (a, tt);
}.

Instance coq_sum_arrow : Arrow Type coq_category void sum := {
  first  x y z (f: x ~> y) a :=
    match a with
    | inl x => inl (f x)
    | inr x => inr x
    end;

  second x y z (f: x ~> y) a :=
    match a with
    | inl x => inl x
    | inr x => inr (f x)
    end;

  assoc x y z a :=
    match a with
    | inl x =>
      match x with
      | inl y => inl y
      | inr y => inr (inl y)
      end
    | inr x => inr (inr x)
    end;

  unassoc x y z a :=
    match a with
    | inl x => inl (inl x)
    | inr x =>
      match x with
      | inl y => inl (inr y)
      | inr y => inr y
      end
    end;

  cancelr x a :=
    match a with
    | inl x => x
    | inr x => match void_is_false x with end
    end;
  cancell x a :=
    match a with
    | inl x => match void_is_false x with end
    | inr x => x
    end;

  uncancell x a := inr a;
  uncancelr x a := inl a;
}.

Instance coq_arrow_sum : Arrows.Sum Type coq_category void sum coq_sum_arrow := {
  merge X x := match x with
    | inl x => x
    | inr x => x
    end;

  never X x := match void_is_false x with end;
}.
