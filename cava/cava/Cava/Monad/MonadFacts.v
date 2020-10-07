Require Import ExtLib.Structures.Monads.
Require Import Cava.Monad.CavaMonad.

Require Import ExtLib.Structures.MonadLaws.
Require Import coqutil.Tactics.Tactics.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Structures.Monad.

Local Open Scope monad_scope.

(* This instance allows the use of functional extensionality on identity-monad
   bind *)
Lemma ident_bind_Proper_ext : forall t u x f g,
  (forall a, f a = g a) ->
  @bind _ Monad_ident t u x f = @bind _ Monad_ident t u x g.
Proof.
  intros. (* Introduce quantified variables.
    t: Type
    u: Type
    x: ident t
    f, g: t -> ident u
    H: forall a : t, f a = g a
    ---------------------------
    ` x : _ <- x;; f x = ` x : _ <- x;; g x   *)
  simpl. (* Simplify to boil down to applications of unIdent
    f (unIdent x) = g (unIdent x) *)
  auto. (* auto can use H in our context to discharge the proof. *)
Qed.

(* Right identity monad law specialized to the identity monad:
  x >>= ret = x  *)
Lemma ident_bind_ret A (x : ident A) : x >>= ret = x.
Proof.
  (* Desugared:
       x : _ <- x;; ret x = x *)
  destruct x. (* Take apart on x
      x : _ <- {| unIdent := unIdent |};;
      ret x = {| unIdent := unIdent |} *)
  simpl. (* Perform unfolding simplifications:
    {| unIdent := unIdent |} = {| unIdent := unIdent |}   *)
  reflexivity.
Qed.

(* Recognize a bind of bind *)
Lemma ident_bind_lift_app {A B C} (f : B -> C) (g : A -> B) x :
  bind (Monad:=Monad_ident) x (fun y => ret (f (g y))) =
  x >>= (fun y => ret (g y)) >>= (fun y => ret (f y)).
Proof.
  destruct x. (* Take apart on x
    y : A <- {| unIdent := unIdent |};; ret (f (g y)) =
    y : A <- {| unIdent := unIdent |};;  y0 : B <- ret (g y);;
                                         ret (f y0)  *)
  reflexivity. (* y0 is g y, so f y0 is f (g y) *)
Qed.

Hint Rewrite @bind_of_return @bind_associativity
     using solve [typeclasses eauto] : monadlaws.

(* Prove that Monad_ident is an instance of MonadLaw.
   Should this really be in coq-ext-lib? *)
Instance MonadLaws_ident : MonadLaws Monad_ident.
Proof. constructor; intros; reflexivity. Qed.

(* Decompose a serial composition of circuits f and g into
   two separate combinational interpretations. *)
Lemma combinational_bind {A B} (f : ident A) (g : A -> ident B) :
  combinational (f >>= g) = combinational (g (combinational f)).
Proof.
  destruct f. (* Take apart on the circuit f.
    combinational (` x : _ <- {| unIdent := unIdent |};; g x) =
    combinational (g (combinational {| unIdent := unIdent |}))   *)
  reflexivity. (* Both sides boil down to computing x as the result of
                  circuit f which is passed as an argument to circuit g *)
Qed.

(* The combinational interpretation of the `return` of any value is
   just the same value. *)
Lemma combinational_ret {A} (x : A) : combinational (ret x) = x.
Proof. reflexivity. Qed.