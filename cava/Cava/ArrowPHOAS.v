Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq Require Import btauto.Btauto.

Require Import Cava.Arrow.

Set Implicit Arguments.
Set Strict Implicit.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations. 

Section Kappa.
  Context {A: Arrow}.

  Variable var: object -> object -> Type.

  Inductive kappa : object -> object -> Type :=
  | Var : forall x y, var x y -> kappa x y
  | Abs : forall x y z, (var unit x -> kappa y z) -> kappa (product x y) z
  | Compose : forall x y z, kappa y z -> kappa x y -> kappa x z
  | Id : forall x, kappa x x
  | First : forall x y z, kappa x y -> kappa (product x z) (product y z).

End Kappa.

(* Context {A: Arrow}.
Definition Term i o := forall var, kappa var i o.
Definition Foo {i} : Term _ i := fun _ => Abs _ (fun x => Var _ _ _ x).
Definition Bar 
  {i o} : Term i o
  := fun _ =>
  Abs _ (fun x => 
      Abs _ (fun y =>
        Compose (Var _ _ _ x) (Var _ _ _ y))). *)

(* Section LambdaExperimentation.
  Context `{C: Category}.

  Inductive type : Type :=
  | obj (o: object) : type
  | morph (o: object) : type
  | fn : type -> type -> type.

  Variable var: type -> Type.

  Inductive lambda : type -> Type :=
  | Var : forall t, var t -> lambda t
  | Abs : forall x y, (var x -> lambda y) -> lambda (fn x y)
  | App : forall x y, lambda (fn x y) -> lambda x -> lambda y
  | Arr x y (_: morphism x y) : lambda (fn (obj x) (obj y))
  (* TODO: | Let ... *)
  (* TODO: | LetRec ... *)
  .

  Arguments Var _ [var t] _.
  Arguments Abs _ [var x y] _.

  Definition Var' {t:type} {var} (x:_) := @Var _ var t x.

  Definition Term t := forall var, lambda var t.

  Check Term.

  Definition Foo {x} : Term (fn x x) := fun _ => Abs _ (fun x => Var' x).
  Definition Bar {x y} : Term (fn (fn y x) (fn y x))
  := fun _ =>
  Abs _ (fun x => 
      Abs _ (fun y =>
        App (Var' x) (Var' y))).
  Definition Baz {a b} (arr: a~>b): Term (fn (obj a) (obj b))
  := fun _ => Abs _ (fun x => App (Arr _ _ _ arr) (Var' x)).

  Declare Scope lambda_notation.
  Delimit Scope lambda_notation with lambda.
  Declare Scope lambda_expr_notation.
  Delimit Scope lambda_expr_notation with lambda_expr.

  Notation "'rebind_variable' x e" := (let x := @Var _ _ _ x in (e) )
    % lambda_expr
    (at level 61, x at level 0, e at next level, no associativity) : lambda_notation.

  Notation "\ x => e " := (Abs _ (fun x => (rebind_variable x e))) % lambda
    (at level 61, e at next level, right associativity) : lambda_notation.

  Notation "'id' x" := (App (@Arr _ _ _ _ id) x)
    %lambda_expr
    (at level 61, no associativity) : lambda_expr_notation.

  Eval simpl in Foo.
  Eval simpl in ( \x => x )%lambda.
  Eval simpl in ( \y => y )%lambda.
  Eval simpl in ( \y => \x => App y x )%lambda.

  Fixpoint countVars t (e : lambda (fun _ => Datatypes.unit) t) : nat :=
  match e with
  | Var _ _ => 1
  | Arr _ _ _ _ => 0
  | Abs _ e1 => countVars (e1 tt)
  | App e1 e2 => countVars e1 + countVars e2
  end.
  Definition CountVars t (E : Term t) := countVars (E (fun _ => Datatypes.unit)).

  Eval compute in CountVars (fun _ => (
    \x => \y => 
      App y (id x)
    )%lambda).

End LambdaExperimentation. *)