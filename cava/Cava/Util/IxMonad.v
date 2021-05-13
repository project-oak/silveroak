Require Import ExtLib.Structures.Monoid.

(* Set Universe Polymorphism. *)

(* Dominic Orchard style indexed monad *)
(* TODO(blaxill): switch to Atkey or McBride ? *)
Class IxMonad {x} (eff: Monoid x) (m : x -> Type -> Type) : Type :=
{ ret : forall {a}, a -> m (monoid_unit eff) a
; bind : forall {a b s t}, m s a -> (a -> m t b) -> m (monoid_plus eff s t) b
}.

Class IxMonadFix {x} (eff: Monoid x) (m : x -> Type -> Type) : Type :=
{ mfix : forall {a b s}, ((a -> m s b) -> a -> m s b) -> a -> m s b }.

Definition mcompose {x} {eff: Monoid x} {m} {M: IxMonad eff m}
           {T U V:Type} {a b}
           (f: T -> m a U) (g: U -> m b V): (T -> m (monoid_plus eff a b) V) :=
  fun x => bind (f x) g.

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
