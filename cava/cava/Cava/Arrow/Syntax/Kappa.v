Require Import List Lia.

Import ListNotations.

Require Import Cava.Arrow.Arrow.

Reserved Infix "<-->" (at level 90, no associativity).

Section WithArrow.
  Variable arr: Arrow.

  Section Vars.
    Variable var: object -> object -> Type.

    Inductive kappa_sugared : object -> object -> Type :=
    | Var: forall x y,    var x y -> kappa_sugared x y
    | Abs: forall x y z,  (var unit x -> kappa_sugared y z) -> kappa_sugared (x**y) z
    | App: forall x y z,  kappa_sugared (x**y) z -> kappa_sugared unit x -> kappa_sugared y z
    | Com: forall x y z,  kappa_sugared y z -> kappa_sugared x y -> kappa_sugared x z
    | Arr: forall x y,    morphism x y -> kappa_sugared x y
    | Let: forall x y z,  kappa_sugared unit x -> (var unit x -> kappa_sugared y z) -> kappa_sugared y z 
    | Iso: forall x y z,  kappa_sugared y z -> obj_equiv x y -> kappa_sugared x z
    .
  End Vars.

  Definition Kappa_sugared i o := forall var, @kappa_sugared var i o.

End WithArrow.

Arguments Var [arr var x y].
Arguments Abs [arr var x y z].
Arguments App [arr var x y z].
Arguments Com [arr var x y z].
Arguments Arr [arr var x y].
Arguments Let [arr var x y z].
Arguments Iso [arr var x y z].

Arguments kappa_sugared [arr].
Arguments Kappa_sugared [arr].
