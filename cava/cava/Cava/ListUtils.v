Require Import Coq.Lists.List.

(* Proofs about fold_right and fold_left *)
Section Folds.
  Context {A : Type}.

  Lemma fold_left_assoc (f : A -> A -> A) id
        (right_identity : forall a, f a id = a)
        (left_identity : forall a, f id a = a)
        (associative :
           forall a b c, f a (f b c) = f (f a b) c) :
    forall l start,
      fold_left f l start = f start (fold_left f l id).
  Proof.
    induction l; cbn [fold_left]; intros.
    { rewrite right_identity. reflexivity. }
    { rewrite left_identity.
      rewrite IHl, <-associative, <-IHl.
      reflexivity. }
  Qed.
End Folds.

Ltac destruct_lists_by_length :=
  repeat
    match goal with
    | H : length ?l = S _ |- _ =>
      destruct l; cbn [length] in *; [ congruence | apply eq_add_S in H ]
    | H : length ?l = 0 |- _ =>
      destruct l; cbn [length] in *; [ | congruence ]
    end.

Section DestructListsByLengthTests.
  (* list with length 0 *)
  Goal (forall (l : list nat),
           length l = 0 -> l = nil).
  Proof.
    intros. destruct_lists_by_length.
    (* since l should be destructed, [nil=nil] should be left over *)
    exact (eq_refl nil).
  Qed.

  (* list with length (S n) *)
  Goal (forall (l : list nat) (n : nat),
           length l = S n -> length (tl l) = n).
  Proof.
    intros. destruct_lists_by_length.
    (* we should now have an expression of the form tl (_ :: _) *)
    progress cbn [tl]. assumption.
  Qed.

  (* multiple constant-length lists *)
  Goal (forall (l1 l2 : list nat),
           length l1 = 1 ->
           length l2 = 2 ->
           length (l1 ++ l2) = 3).
  Proof.
    intros. destruct_lists_by_length.
    (* now, we expect l1 and l2 to be fully destructed *)
    match goal with
    | |- length ((_ :: nil) ++ (_ :: _ :: nil)) = 3 => idtac
    end.
    reflexivity.
  Qed.
End DestructListsByLengthTests.
