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

Generalizable All Variables.

Definition build_denoted_kleisli_category T denote m (M: Monad m): Category T :=
{|
  morphism X Y := denote X -> m (denote Y);
  id X := ret;
  compose X Y Z f g := g >=> f;
|}.

Program Definition build_denoted_kleisli_arrow T denote m (M: Monad m) unit tuple
  (tt: denote unit)
  (pair: forall {x y}, denote x -> denote y -> denote (tuple x y))
  (fst: forall {x y}, denote (tuple x y) -> denote x)
  (snd: forall {x y}, denote (tuple x y) -> denote y)
  : Arrow T (build_denoted_kleisli_category T denote m M) unit tuple :=
{|
  first  x y z f a :=
    b <- f (fst a) ;;
    ret (pair b (snd a));
  second x y z f a :=
    b <- f (snd a) ;;
    ret (pair (fst a) b);

  assoc   x y z := fun a => ret (pair (fst (fst a)) (pair (snd (fst a)) (snd a)));
  unassoc x y z := fun a => ret (pair (pair (fst a) (fst (snd a))) (snd (snd a)));

  cancelr x := fun a => ret (fst a);
  cancell x := fun a => ret (snd a);

  uncancell x := fun a => ret (pair tt a);
  uncancelr x := fun a => ret (pair a tt);
|}.

Definition kleisli_category m (M: Monad m) : Category Type
  := build_denoted_kleisli_category Type (fun x => x) m M.

Definition kleisli_arrow m (M: Monad m) : Arrow Type (kleisli_category m M) unit prod
  := build_denoted_kleisli_arrow Type (fun x => x) m M unit prod
  tt (fun _ _ => pair) (fun _ _ => fst) (fun _ _ => snd).

Instance kleisli_sum_arrow m (M: Monad m): Arrow Type (kleisli_category m M) void sum := {
  first x y z (f: x ~> y) a :=
    match a with
    | inl x =>
      x' <- f x ;;
      ret (inl x')
    | inr x => ret (inr x)
    end;

  second x y z (f: x ~> y) a :=
    match a with
    | inl x => ret (inl x)
    | inr x =>
      x' <- f x ;;
      ret (inr x')
    end;

  assoc x y z a :=
    match a with
    | inl x =>
      match x with
      | inl y => ret (inl y)
      | inr y => ret (inr (inl y))
      end
    | inr x => ret (inr (inr x))
    end;

  unassoc x y z a :=
    match a with
    | inl x => ret (inl (inl x))
    | inr x =>
      match x with
      | inl y => ret (inl (inr y))
      | inr y => ret (inr y)
      end
    end;

  cancelr x a :=
    match a with
    | inl x => ret x
    | inr x => match void_is_false x with end
    end;
  cancell x a :=
    match a with
    | inl x => match void_is_false x with end
    | inr x => ret x
    end;

  uncancell x a := ret (inr a);
  uncancelr x a := ret (inl a);
}.

Instance kleisli_arrow_sum m (M: Monad m):
  Arrows.Sum Type (kleisli_category m M) void sum (kleisli_sum_arrow m M) := {
  merge X x := match x with
    | inl x => ret x
    | inr x => ret x
    end;

  never X x := match void_is_false x with end;
}.

