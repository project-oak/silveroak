
Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Arrow.

From Coq Require Import NArith.

Import KappaNotation.

Section var.

Context {var: Kind -> Kind -> Type}.

Fixpoint reduce {n T}
  (f : kappa_sugared var <<T, T, Unit>> T)
  {struct n}
  : kappa_sugared var << Vector (S n) T, Unit >> <<T>> :=
match n with
| 0 => <[ \x => x[#0] ]>
| S n' => 
  <[ \xs =>
      let '(x, xs') = !(kappa_head') xs in
      let y = !(reduce f) xs' in
      !f x y 
  ]>
end.

Fixpoint map2_xor {n}
  : kappa_sugared var << Vector (S n) Bit, Vector (S n) Bit, Unit >> <<Vector (S n) Bit>> :=
match n with
| 0 => <[ \x y => mkVec (xor (x[#0]) (y[#0])) ]> 
| S n' =>
  <[ \xs ys =>
      let '(x, xs') = !kappa_head' xs in
      let '(y, ys') = !kappa_head' ys in
      concat
        (mkVec ( xor x y ))
        (!(@map2_xor n') xs' ys')
  ]> 
end.

End var.