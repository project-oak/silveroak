From Coq Require Import List PeanoNat Arith.Peano_dec.
From Cava Require Import Arrow.ArrowKind Arrow.ExprSyntax.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

  Section Equivalence.
    Variables var1 var2 : Kind -> Type.

    Definition vars := existT (fun t => (var1 t * var2 t)%type).
    Definition ctxt := list { t : Kind & (var1 t * var2 t)%type }.

    Inductive kappa_equivalence:
      forall i o, ctxt
      -> kappa var1 i o -> kappa var2 i o
      -> Prop :=
    | Var_equiv : forall x (n1: var1 x) (n2: var2 x) E,
      In (vars (pair n1 n2)) E
      -> kappa_equivalence E (Var n1) (Var n2)

    | Abs_equiv : forall x y z
      (f1: var1 x -> kappa var1 y z)
      (f2: var2 x -> kappa var2 y z)
      (E: ctxt),
      (forall n1 n2, kappa_equivalence (vars (pair n1 n2) :: E) (f1 n1) (f2 n2))
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

    | Let_equiv : forall x y z
      (v1: kappa var1 Unit x)
      (v2: kappa var2 Unit x)
      (f1: var1 x -> kappa var1 y z)
      (f2: var2 x -> kappa var2 y z)
      (E: ctxt),
      kappa_equivalence E v1 v2
      ->
      (forall n1 n2, kappa_equivalence (vars (pair n1 n2) :: E) (f1 n1) (f2 n2))
      ->
      kappa_equivalence E (Let v1 f1) (Let v2 f2)

    | Letrec_equiv : forall x y z
      (v1: var1 x -> kappa var1 Unit x)
      (v2: var2 x -> kappa var2 Unit x)
      (f1: var1 x -> kappa var1 y z)
      (f2: var2 x -> kappa var2 y z)
      (E: ctxt),
      (forall n1 n2, kappa_equivalence (vars (pair n1 n2) :: E) (v1 n1) (v2 n2))
      ->
      (forall n1 n2, kappa_equivalence (vars (pair n1 n2) :: E) (f1 n1) (f2 n2))
      ->
      kappa_equivalence E (LetRec v1 f1) (LetRec v2 f2)

    | Id_equiv : forall x E, kappa_equivalence E (@Id var1 x) Id

    | RemoveContext_equiv : forall x y E
      (f1 : kappa var1 x y)
      (f2 : kappa var2 x y),
      kappa_equivalence nil f1 f2
      ->
      kappa_equivalence E (RemoveContext f1) (RemoveContext f2)
    .

  End Equivalence.

  Definition Wf {i o} (e: Kappa i o) := forall var1 var2, kappa_equivalence [] (e var1) (e var2).
