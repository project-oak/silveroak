From Arrow Require Import Category Arrow.

Section Arrow.
  Context `{A: ArrowSTKC}.

  Section Vars.
    Variable (var: object -> object -> Type).

    Local Open Scope arrow_scope.

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
  End Vars.

  Definition Kappa i o := forall var, kappa var i o.
End Arrow.