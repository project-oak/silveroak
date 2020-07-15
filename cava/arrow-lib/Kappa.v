From Arrow Require Import Category Arrow.

Section Arrow.
  Context `{A: ArrowSTKC}.

  Section Vars.
    Variable (var: object -> object -> Type).

    Local Open Scope arrow_scope.
    Local Open Scope category_scope.

    Inductive kappa : object -> object -> Type :=
    | Var : forall {x y},   var x y -> kappa x y
    | Abs : forall x {y z}, (var u x -> kappa y z) -> kappa (x ** y) z
    | App : forall {x y z}, kappa (x ** y) z -> kappa u x -> kappa y z
    | Comp: forall {x y z}, kappa y z -> kappa x y -> kappa x z
    | Morph : forall {x y}, morphism x y -> kappa x y
    | LetRec : forall x {y z}, 
        (var u x -> kappa u x)
      -> (var u x -> kappa y z) 
      -> kappa y z.

    Inductive NoLetRecKappa: forall i o, kappa i o -> Prop :=
    | NoLetRecVar: forall x y v, NoLetRecKappa x y (Var v)
    | NoLetRecAbs: forall x y z f,
      (forall (k: var u x), NoLetRecKappa y z (f k)) -> NoLetRecKappa (x**y) z (Abs _ f)
    | NoLetRecApp: forall x y z f e,
      NoLetRecKappa (x ** y) z f -> NoLetRecKappa u x e -> NoLetRecKappa y z (App f e)
    | NoLetRecComp: forall x y z f g,
      NoLetRecKappa y z f -> NoLetRecKappa x y g -> NoLetRecKappa x z (Comp f g)
    | NoLetRecMorph : forall x y m, NoLetRecKappa x y (Morph m).

    Section prop.
      Variable (P: forall x y, morphism x y -> Prop).

      Inductive MorphPropKappa: forall i o, kappa i o -> Prop :=
      | MorphPropVar: forall x y v, MorphPropKappa x y (Var v)
      | MorphPropAbs: forall x y z f, (forall (k: var u x), MorphPropKappa y z (f k)) -> MorphPropKappa (x**y) z (Abs _ f)
      | MorphPropApp: forall x y z f e,
        MorphPropKappa (x ** y) z f -> MorphPropKappa u x e -> MorphPropKappa y z (App f e)
      | MorphPropComp: forall x y z f g,
        MorphPropKappa y z f -> MorphPropKappa x y g -> MorphPropKappa x z (Comp f g)
      | MorphPropMorph : forall x y m, P x y m -> MorphPropKappa x y (Morph m).

    End prop.

  End Vars.

  Definition Kappa i o := forall var, kappa var i o.

End Arrow.