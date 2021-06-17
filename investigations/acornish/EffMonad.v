Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.List.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

(* Dominic Orchard style graded/indexed monad *)
(* See "Embedding Effect Systems in Haskell"
   http://www.cl.cam.ac.uk/~dao29/publ/haskell14-effects.pdf *)
Section indexed.
  Context {x : Type}.
  Context {eff: Monoid x}.

  Class EffFunctor (f : x -> Type -> Type) : Type :=
  { fmap : forall {a b i}, (a -> b) -> f i a -> f i b }.

  Class EffApplicative (t : x -> Type -> Type) :=
  {
    (* applicative_is_functor :> EffFunctor t *)
    pure : forall {a}, a -> t (monoid_unit eff) a
  ; ap : forall {a b m n}, t m (a -> b) -> t n a -> t (monoid_plus eff m n) b
  }.

  Class EffMonad (m : x -> Type -> Type) : Type :=
  {
    (* monad_is_applicative :> EffApplicative m *)
    ret : forall {a}, a -> m (monoid_unit eff) a
  ; bind : forall {a b s t}, m s a -> (a -> m t b) -> m (monoid_plus eff s t) b
  }.

  Class EffMonadFix {x} (eff: Monoid x) (m : x -> Type -> Type) : Type :=
  { mfix : forall {a b s}, ((a -> m s b) -> a -> m s b) -> a -> m s b }.

  Definition mcompose {m} {M: EffMonad m}
             {T U V:Type} {a b}
             (f: T -> m a U) (g: U -> m b V): (T -> m (monoid_plus eff a b) V) :=
    fun x => bind (f x) g.

  (* Class EffTraversable (t : Type -> Type) : Type := *)
  (* { traverse_effect : forall {a}, t a -> x -> x *)
  (* ; mapT : forall {f : x -> Type -> Type} {Ap:EffApplicative f} {a b m}, *)
  (*     (a -> f m b) -> forall (i: t a), f (traverse_effect i m) (t b) *)
  (* }. *)
End indexed.

Module EffMonadNotation.
  Declare Scope eff_monad_scope.
  Delimit Scope eff_monad_scope with eff_monad.

  Notation "c >>= f" := (bind c f) (at level 58, left associativity) : eff_monad_scope.
  Notation "f =<< c" := (bind c f) (at level 61, right associativity) : eff_monad_scope.
  Notation "f >=> g" := (mcompose f g) (at level 61, right associativity) : eff_monad_scope.

  Notation "e1 ;; e2" := (bind e1%eff_monad (fun _ => e2%eff_monad))%eff_monad
    (at level 61, right associativity) : eff_monad_scope.

  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : eff_monad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (bind c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : eff_monad_scope.
End EffMonadNotation.

Module EffFunctorNotation.
  Notation "f <$> x" := (fmap f x) (at level 52, left associativity).
End EffFunctorNotation.

Module EffApplicativeNotation.
  Notation "f <*> x" := (ap f x) (at level 52, left associativity).
End EffApplicativeNotation.
