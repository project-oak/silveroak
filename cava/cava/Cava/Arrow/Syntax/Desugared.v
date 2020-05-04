Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Syntax.Kappa.

Reserved Infix "<-->" (at level 90, no associativity).
Reserved Infix "≅" (at level 90, no associativity).
Reserved Infix "--->" (at level 90, no associativity).

Section WithArrow.
  Variable arr: Arrow.

  Section Vars.
    Variable var: object -> object -> Type.

    (* desugared, currently only let removal *)
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

  (* currently only desugars let bindings *)
  Fixpoint desugar {var i o} (e: kappa_sugared var i o) : kappa var i o :=
  match e with
  | Var x => DVar x
  | Abs f => DAbs (fun x => desugar (f x))
  | App e1 e2 => DApp (desugar e1) (desugar e2)
  | Compose f g => DCompose (desugar f) (desugar g)
  | Arr m => DArr m
  | Let x f => DApp (DAbs (fun x => desugar (f x))) (desugar x)
  end.

  Definition Desugar {i o} (e: Kappa_sugared i o) : Kappa i o := fun var => desugar (e var).

  Fixpoint kappa_reinject {var i o} (e: kappa var i o) : kappa_sugared var i o :=
  match e with
  | DVar x => Var x
  | DAbs f => Abs (fun x => kappa_reinject (f x))
  | DApp e1 e2 => App (kappa_reinject e1) (kappa_reinject e2)
  | DCompose f g => Compose (kappa_reinject f) (kappa_reinject g)
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