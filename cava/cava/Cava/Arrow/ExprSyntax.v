From Coq Require Import Lists.List.
From Coq Require Import Arith.Peano_dec.
From Cava Require Import Arrow.ArrowKind.
From Cava Require Import Arrow.Primitives.
From Arrow Require Import Category.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section vars.
  Definition natvar : Kind -> Kind -> Type := fun _ _ => nat.
  Definition unitvar : Kind -> Kind -> Type := fun _ _ => unit.

  Section Vars.
    Variable (var: Kind -> Kind -> Type).

    Inductive kappa : Kind -> Kind -> Type :=
    | Var : forall {x y},   var x y -> kappa x y
    | Abs : forall {x y z}, (var Unit x -> kappa y z) -> kappa (Tuple x y) z
    | App : forall {x y z}, kappa (Tuple x y) z -> kappa Unit x -> kappa y z
    | Comp: forall {x y z}, kappa y z -> kappa x y -> kappa x z
    | Primitive : forall prim, kappa (primitive_input prim) (primitive_output prim)
    | Let: forall {x y z}, kappa Unit x -> (var Unit x -> kappa y z) -> kappa y z
    | LetRec : forall {x y z}, (var Unit x -> kappa Unit x) -> (var Unit x -> kappa y z) -> kappa y z
    | Id : forall {x}, kappa x x
    .
  End Vars.

  Fixpoint reverse_nth {A} (l: list A) (n: nat) {struct l}: option A :=
    match l with
    | [] => None
    | x :: xs =>
      match eq_nat_dec n (length xs) with
      | left _ => Some x
      | right Hneq => reverse_nth xs n
      end
    end.

  Notation ok_lookup := (fun (l: list _) (n: nat) (ty: _) => reverse_nth l n = Some ty).

  Fixpoint wf_phoas_context {i o}
    (ctxt: list Kind)
    (expr: kappa natvar i o) {struct expr}
    : Prop :=
    match expr with
    | Var _ _ n  => ok_lookup ctxt n o
    | Abs x _ _ f => wf_phoas_context (x :: ctxt) (f (length ctxt))
    | App _ _ _ e1 e2 => wf_phoas_context ctxt e1 /\ wf_phoas_context ctxt e2
    | Comp _ _ _ e1 e2 => wf_phoas_context ctxt e1 /\ wf_phoas_context ctxt e2
    | Primitive _ => True
    | Id _ => True
    | Let x _ _ v f => wf_phoas_context (x :: ctxt) (f (length ctxt)) /\ wf_phoas_context ctxt v
    | LetRec x _ _ v f => wf_phoas_context (x :: ctxt) (v (length ctxt)) /\ wf_phoas_context (x :: ctxt) (f (length ctxt))
    end.

  Definition Kappa i o := forall var, kappa var i o.

End vars.

Arguments Var {var _ _}.
Arguments Abs {var _ _ _}.
Arguments App {var _ _ _}.
Arguments Comp {var _ _ _}.
Arguments Primitive {var}.
Arguments LetRec {var _ _ _}.
Arguments Id {var _}.

Instance KappaCat : Category Kind := {
  morphism X Y := forall var, kappa var X Y;
  id X := fun var => @Id var X;
  compose X Y Z f g := fun var => Comp (f var) (g var);
}.
