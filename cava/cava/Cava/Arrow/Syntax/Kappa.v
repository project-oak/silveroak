Require Import Cava.Arrow.Arrow.

Section WithArrow.
  Variable arr: Arrow.

  Section Vars.
    Variable var: object -> object -> Type.

    Inductive kappa_sugared : object -> object -> Type :=
    | Var : forall x y,     var x y -> kappa_sugared x y
    | Abs : forall x y z,   (var unit x -> kappa_sugared y z) -> kappa_sugared (x**y) z
    | App : forall x y z,   kappa_sugared (x**y) z -> kappa_sugared unit x -> kappa_sugared y z
    | Compose : forall x y z, kappa_sugared y z -> kappa_sugared x y -> kappa_sugared x z
    | Arr : forall x y,     morphism x y -> kappa_sugared x y
    | Let : forall x y z,   kappa_sugared unit x -> (var unit x -> kappa_sugared y z) -> kappa_sugared y z .
  End Vars.

  Definition Kappa_sugared i o := forall var, @kappa_sugared var i o.

  (* TODO: enable transforms? *)
  (* Reserved Infix "<-->" (at level 90, no associativity). *)
  (* Reserved Infix "≅" (at level 90, no associativity). *)
  (* Reserved Infix "--->" (at level 90, no associativity). *)
  (* (1* Non-destructive transform / isomorphism *1) *)
  (* Inductive iso : object -> object -> Type := *)
  (* | IId:          forall x,     x <--> x *)
  (* | ICancelL:     forall x,     (unit ** x) <--> x *)
  (* | ICancelR:     forall x,     (x ** unit) <--> x *)
  (* | IUncancelL:   forall x,     x <--> (unit ** x) *)
  (* | IUncancelR:   forall x,     x <--> (x ** unit) *)

  (* | IAssociate:   forall x y z, ((x ** y) ** z) <--> (x ** (y ** z)) *)
  (* | IUnassociate: forall x y z, (x ** (y ** z)) <--> ((x ** y) ** z) *)
  (* where "x <--> y" := (iso x y). *)

  (* Inductive iso_closure: object -> object -> Type := *)
  (* | IIso:     forall x y,     x <--> y -> x ≅ y *)
  (* | ICompose: forall x y z,   x <--> y -> y <--> z -> x ≅ z *)
  (* (1* | IProduct: forall x y z w, x <--> y -> z <--> w -> x**z ≅ y**w *1) *)
  (* where "x ≅ y" := (iso_closure x y). *)

  (* (1* Destructive object re-arrangement rules *1) *)
  (* Inductive arrange : object -> object -> Type := *)
  (* | ALeft:    forall x z,   (z ** x) ---> x *)
  (* | ARight:   forall x z,   (x ** z) ---> x *)
  (* | AWeak:    forall x,     x ---> unit *)

  (* | AIso:     forall x y,   x <--> y -> x ---> y *)
  (* | ACompose: forall x y z, x ---> y -> y ---> z -> x ---> z *)
  (* where "x ---> y" := (arrange x y). *)

End WithArrow.

Arguments Var [arr var x y].
Arguments Abs [arr var x y z].
Arguments App [arr var x y z].
Arguments Compose [arr var x y z].
Arguments Arr [arr var x y].
Arguments Let [arr var x y z].

Arguments kappa_sugared [arr].
Arguments Kappa_sugared [arr].
