Class Monad (m : Type -> Type) : Type := { 
    ret : forall {t}, t -> m t ;
    bind : forall {t u}, m t -> (t -> m u) -> m u
}.

Class MonadState (T : Type) (m : Type -> Type) : Type := {
    get : m T ;
    put : T -> m unit
}.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

Definition state := nat.
Definition state_comp(A:Type) := state -> (state*A).

Instance StateMonad : Monad state_comp := {
  ret := fun {A:Type} (x:A) => (fun (s:state) => (s,x)) ;
  bind := fun {A B:Type} (c : state_comp A) (f: A -> state_comp B) =>
            fun (s:state) =>
              let (s',v) := c s in
              f v s'
}.

Definition read : state_comp nat :=
  fun s => (s, s).

Definition write (n:nat) : state_comp nat :=
  fun s => (n, n).

