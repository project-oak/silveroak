Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Syntax.Kappa.

Reserved Infix "<-->" (at level 90, no associativity).
Reserved Infix "≅" (at level 90, no associativity).
Reserved Infix "--->" (at level 90, no associativity).

Section WithArrow.
  Variable arr: Arrow.

  Section Vars.
    Variable var: object -> object -> Type.

    Inductive kappa : object -> object -> Type :=
    | DVar : forall x y,   var x y -> kappa x y
    | DAbs : forall x y z, (var unit x -> kappa y z) -> kappa (x**y) z
    | DApp : forall x y z, kappa (x**y) z -> kappa unit x -> kappa y z
    | DCompose : forall x y z, kappa y z -> kappa x y -> kappa x z
    | DArr : forall x y,   morphism x y -> kappa x y.
  End Vars.

  Arguments DVar [var x y].
  Arguments DAbs [var x y z].
  Arguments DApp [var x y z].
  Arguments DCompose [var x y z].
  Arguments DArr [var x y].

  Definition Kappa i o := forall var, @kappa var i o.

  (* desugars 
  - let 
  - object equivalence (iso)
  *)
  Fixpoint desugar {var i o} (e: kappa_sugared var i o) : kappa var i o :=
  match e with
  | Var x => DVar x
  | Abs f => DAbs (fun x => desugar (f x))
  | App e1 e2 => DApp (desugar e1) (desugar e2)
  | Com f g => DCompose (desugar f) (desugar g)
  | Arr m => DArr m
  | Let x f => DApp (DAbs (fun x => desugar (f x))) (desugar x)
  | Iso f iso => DCompose (desugar f) (DArr (apply_object_equivalence_left arr _ _ iso)) 
  end.

  Definition Desugar {i o} (e: Kappa_sugared i o) : Kappa i o := fun var => desugar (e var).

  Fixpoint kappa_project {var i o} (e: kappa var i o) : kappa_sugared var i o :=
  match e with
  | DVar x => Var x
  | DAbs f => Abs (fun x => kappa_project (f x))
  | DApp e1 e2 => App (kappa_project e1) (kappa_project e2)
  | DCompose f g => Com (kappa_project f) (kappa_project g)
  | DArr m => Arr m
  end.
End WithArrow.

Arguments DVar [arr var x y].
Arguments DAbs [arr var x y z].
Arguments DApp [arr var x y z].
Arguments DCompose [arr var x y z].
Arguments DArr [arr var x y].

Arguments kappa [arr].
Arguments Kappa [arr].