Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.List.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Section indexed.
  Context {x : Type}.

  Class IxMonad (m : x -> x -> Type -> Type) : Type :=
  {
    (* monad_is_applicative :> IxApplicative m *)
    ret : forall {a s}, a -> m s s a
  ; bind : forall {a b s t u}, m s t a -> (a -> m t u b) -> m s u b
  }.


  Definition mcompose {m} {M: IxMonad m} {a b c s t u}
             (f: a -> m s t b) (g: b -> m t u c): (a -> m s u c) :=
    fun x => bind (f x) g.

End indexed.

Module IxMonadNotation.
  Declare Scope ix_monad_scope.
  Delimit Scope ix_monad_scope with ix_monad.

  Notation "c >>= f" := (bind c f) (at level 58, left associativity) : ix_monad_scope.
  Notation "f =<< c" := (bind c f) (at level 61, right associativity) : ix_monad_scope.
  Notation "f >=> g" := (mcompose f g) (at level 61, right associativity) : ix_monad_scope.

  Notation "e1 ;; e2" := (bind e1%ix_monad (fun _ => e2%ix_monad))%ix_monad
    (at level 61, right associativity) : ix_monad_scope.

  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : ix_monad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (bind c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : ix_monad_scope.
End IxMonadNotation.
