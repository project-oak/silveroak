From ExtLib Require Import Structures.Monads.
From Arrow Require Import Category Arrow.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope category_scope.

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

Instance coq_arrow_sum : ArrowSum Type coq_category void sum coq_sum_arrow := {
  merge X x := match x with
    | inl x => x
    | inr x => x
    end;

  never X x := match void_is_false x with end;
}.