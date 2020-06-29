From ExtLib Require Import Structures.Monads.
From Arrow Require Import Category Arrow.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope category_scope.

Generalizable All Variables.

Instance kleisli_category m (M: Monad m) : Category Type := {
  morphism X Y := X -> m Y;
  id := @ret m M;
  compose X Y Z f g := g >=> f;
}.

Instance kleisli_arrow m (M: Monad m) : Arrow Type (kleisli_category m M) unit prod := {
  first  x y z (f: x ~> y) a := 
    b <- f (fst a) ;;
    ret (b, snd a);
  second x y z (f: x ~> y) a := 
    b <- f (snd a) ;;
    ret (fst a, b);

  assoc   x y z a := ret (fst (fst a), (snd (fst a), snd a));
  unassoc x y z a := ret ((fst a, fst (snd a)), snd (snd a));

  cancelr x a := ret (fst a);
  cancell x a := ret (snd a);

  uncancell x a := ret (tt, a);
  uncancelr x a := ret (a, tt);
}.

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
  ArrowSum Type (kleisli_category m M) void sum (kleisli_sum_arrow m M) := {
  merge X x := match x with
    | inl x => ret x 
    | inr x => ret x 
    end;

  never X x := match void_is_false x with end;
}.

