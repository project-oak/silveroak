From Coq Require Import List PeanoNat Arith.Peano_dec.
From Cava Require Import Arrow.ArrowKind Arrow.ExprSyntax.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

  Section Equivalence.
    Inductive obj_tup : Type := obj_pair : Kind -> Kind -> obj_tup.
    Variables var1 var2 : Kind -> Kind -> Type.

    Definition vars := existT (fun '(obj_pair x y) => (var1 x y * var2 x y)%type).
    Definition ctxt := list { '(obj_pair x y) : obj_tup & (var1 x y * var2 x y)%type }.

    Inductive kappa_equivalence:
      forall i o, ctxt
      -> kappa var1 i o -> kappa var2 i o
      -> Prop :=
    | Var_equiv : forall i o (n1: var1 i o) (n2: var2 i o) E,
      In (vars (obj_pair i o) (pair n1 n2)) E
      -> kappa_equivalence E (Var n1) (Var n2)

    | Abs_equiv : forall x y z
      (f1: var1 Unit x -> kappa var1 y z)
      (f2: var2 Unit x -> kappa var2 y z)
      (E: ctxt),
      (forall n1 n2, kappa_equivalence (vars (obj_pair Unit x) (pair n1 n2) :: E) (f1 n1) (f2 n2))
      -> kappa_equivalence E (Abs f1) (Abs f2)

    | App_equiv : forall E x y z
      (f1 : kappa var1 (Tuple x y) z)
      (f2 : kappa var2 (Tuple x y) z)
      e1 e2,
      kappa_equivalence E f1 f2
      -> kappa_equivalence E e1 e2
      -> kappa_equivalence E (App f1 e1) (App f2 e2)

    | Compose_equiv : forall E x y z
      (f1: kappa var1 y z) (f2: kappa var2 y z)
      (g1: kappa var1 x y) (g2: kappa var2 x y),
      kappa_equivalence E f1 f2
      -> kappa_equivalence E g1 g2
      -> kappa_equivalence E (Comp f1 g1) (Comp f2 g2)

    | Prim_equiv : forall E p, kappa_equivalence E (ExprSyntax.Primitive p) (ExprSyntax.Primitive p)

    | Letrec_equiv : forall x y z
      (v1: var1 Unit x -> kappa var1 Unit x)
      (v2: var2 Unit x -> kappa var2 Unit x)
      (f1: var1 Unit x -> kappa var1 y z)
      (f2: var2 Unit x -> kappa var2 y z)
      (E: ctxt),
      (forall n1 n2, kappa_equivalence (vars (obj_pair Unit x) (pair n1 n2) :: E) (v1 n1) (v2 n2))
      ->
      (forall n1 n2, kappa_equivalence (vars (obj_pair Unit x) (pair n1 n2) :: E) (f1 n1) (f2 n2))
      ->
      kappa_equivalence E (LetRec v1 f1) (LetRec v2 f2)

    | Id_equiv : forall x E, kappa_equivalence E (@Id var1 x) Id
    .

  End Equivalence.

  Definition Wf {i o} (e: Kappa i o) := forall var1 var2, kappa_equivalence [] (e var1) (e var2).

  Axiom Kappa_equivalence : forall {i o} (expr: forall var, kappa var i o), Wf expr.
(* End Arrow. *)
