Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

From Coq Require Import ZArith.

Require Import Cava.Arrow.Arrow.

(* Arrow as function evaluation, no delay elements or loops *)
Section CoqEval.
  Instance CoqCat : Category := {
    morphism X Y := X -> Y;
    compose _ _ _ f g x := f (g x);
    id X x := x;
  }.

  Instance CoqArr : Arrow := {
    unit := Datatypes.unit : Type;
    product := prod;

    fork _ _ _ f g x := (f x, g x);
    exl X Y := fst;
    exr X Y := snd;

    drop _ x := tt;
    copy _ x := pair x x;

    swap _ _ x := (snd x, fst x);

    uncancell _ x := (tt, x);
    uncancelr _ x := (x, tt);

    assoc _ _ _ '((x,y),z) := (x,(y,z));
    unassoc _ _ _ '(x,(y,z)) := ((x,y),z);
  }.

  Instance CoqCava : Cava := {
    bit := bool;

    fromBool b _ := b;

    not_gate b := negb b;
    and_gate '(x,y) := andb x y;
  }.

  Eval cbv in not_gate true.
  Eval cbv in not_gate false.
End CoqEval.
