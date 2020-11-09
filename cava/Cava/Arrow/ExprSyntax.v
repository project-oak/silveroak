From Coq Require Import String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Peano_dec.
From Cava Require Import Arrow.ArrowKind.
From Cava Require Import Arrow.Primitives.
From Cava Require Import Arrow.Classes.Category.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section vars.
  Definition natvar : Kind -> Type := fun _ => nat.
  Definition unitvar : Kind -> Type := fun _ => unit.

  Definition extended_prim_input p :=
    match p with
    | P0 _ _ => Unit
    | P1 x _ _ => Tuple x Unit
    | P2 x y z _ => Tuple x (Tuple y Unit)
    end.

  Record Module ( body_ty : Type ) := mkModule
    { module_name : string
    ; module_body : body_ty
    }.

  Definition module_map_body {A B} (m: Module A) (f: A -> B): Module B :=
    match m with
    | mkModule name body => mkModule name (f body)
    end.

  Section Vars.
    Variable (var: Kind -> Type).

    Inductive kappa : Kind -> Kind -> Type :=
    | Var : forall {x},     var x -> kappa Unit x
    | Abs : forall {x y z}, (var x -> kappa y z) -> kappa (Tuple x y) z
    | App : forall {x y z}, kappa (Tuple x y) z -> kappa Unit x -> kappa y z
    | Comp: forall {x y z}, kappa y z -> kappa x y -> kappa x z
    | Comp1: forall {x y z}, kappa y z -> kappa x (remove_rightmost_unit y) -> kappa x z
    | Delay: forall {x}, kappa (Tuple x Unit) x
    | Primitive : forall prim, kappa (extended_prim_input prim) (primitive_output prim)
    | Let: forall {x y z}, kappa Unit x -> (var x -> kappa y z) -> kappa y z
    | LetRec : forall {x y z}, (var x -> kappa Unit x) -> (var x -> kappa y z) -> kappa y z
    | Id : forall {x}, kappa x x
    | Typecast : forall x y, kappa (Tuple x Unit) y
    | RemoveContext: forall {x y}, kappa x y -> kappa x y
    | CallModule: forall {x y}, Module (kappa x y) -> kappa x y
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
    | Var _ n  => ok_lookup ctxt n o
    | Abs x _ _ f => wf_phoas_context (x :: ctxt) (f (length ctxt))
    | App _ _ _ e1 e2 => wf_phoas_context ctxt e1 /\ wf_phoas_context ctxt e2
    | Comp _ _ _ e1 e2 => wf_phoas_context ctxt e1 /\ wf_phoas_context ctxt e2
    | Comp1 _ _ _ e1 e2 => wf_phoas_context ctxt e1 /\ wf_phoas_context ctxt e2
    | Delay _ => True
    | Primitive _ => True
    | Id _ => True
    | Typecast x y => True
    | Let x _ _ v f => wf_phoas_context (x :: ctxt) (f (length ctxt)) /\ wf_phoas_context ctxt v
    | LetRec x _ _ v f => wf_phoas_context (x :: ctxt) (v (length ctxt)) /\ wf_phoas_context (x :: ctxt) (f (length ctxt))
    | RemoveContext _ _ f => wf_phoas_context [] f
    | CallModule _ _ (mkModule _ m) => wf_phoas_context [] m
    end.

  Definition Kappa i o := forall var, kappa var i o.

  Definition module_instantiate_var {var x y} (m: Module (Kappa x y)): Module (kappa var x y) :=
    module_map_body m (fun e => e var).
End vars.

Arguments Var {var _}.
Arguments Abs {var _ _ _}.
Arguments App {var _ _ _}.
Arguments Comp {var _ _ _}.
Arguments Comp1 {var _ _ _}.
Arguments Delay {var _}.
Arguments Primitive {var}.
Arguments LetRec {var _ _ _}.
Arguments Id {var _}.
Arguments Typecast {var}.
Arguments RemoveContext {var _ _}.
Arguments CallModule {var _ _}.

Instance KappaCat : Category Kind := {
  morphism X Y := forall var, kappa var X Y;
  id X := fun var => @Id var X;
  compose X Y Z f g := fun var => Comp (f var) (g var);
}.
