Require Import Coq.Bool.Bool.

Require Import Cava.Netlist.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "**" (at level 40, left associativity).
Reserved Infix ">>>" (at level 90, right associativity).

(* more flexible than a haskell style category,
  which has morphisms between objects of type Hask.
  Here we have morphisms between objects of type object.
*)
Class Category := {
  object : Type;

  morphism : object -> object -> Type
    where "a ~> b" := (morphism a b);

  id {x} : x ~> x;

  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "g >>> f" := (compose f g);
}.

Declare Scope category_scope.
Bind Scope category_scope with Category.
Delimit Scope category_scope with category.

Notation "x ~> y" := (morphism x y)
  (at level 90, right associativity) : category_scope.
Notation "x ~[ C ]~> y" := (@morphism C x y)
  (at level 90) : category_scope.
Notation "g >>> f" := (compose f g)
  (at level 90, right associativity) : category_scope.

Open Scope category_scope.
Print Category.

(* adam megacz style arrow;
  There is no method to provide lifting a Coq function in general,
  although a particular arrow implementation may allow it.
*)
Class Arrow := {
  cat :> Category;
  unit : object;
  product : object -> object -> object
    where "x ** y" := (product x y);

  copy {x} : x ~> (x**x);
  drop {x} : x ~> unit;
  swap {x y} : (x**y) ~> (y**x);

  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y ** z;
  exl  {x y} : x ** y ~> x;
  exr  {x y} : x ** y ~> y;

  uncancell {x} : x ~> (unit**x);
  uncancelr {x} : x ~> (x**unit);
  assoc {x y z} : ((x**y)**z) ~> (x**(y**z));
  unassoc {x y z} : (x**(y**z)) ~> ((x**y)**z);
}.

Declare Scope arrow_scope.
Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (product x y)
  (at level 40, left associativity) : arrow_scope.

Open Scope arrow_scope.

Definition first {_: Arrow} {x y z} (f : x ~> y) : x ** z ~> y ** z :=
  fork (exl >>> f) exr.

Definition second {_: Arrow} {x y z} (f : x ~> y) : z ** x ~> z ** y :=
  fork exl (exr >>> f).

(* Loop as a different type class to allow implementating a subset of features *)
Class ArrowLoop (A: Arrow) := {
  loopr {x y z} : ((x**z) ~> (y**z)) -> (x ~> y);
  loopl {x y z} : ((z**x) ~> (z**y)) -> (x ~> y);
}.

Print Arrow.

(* Cava *)
Class Cava  := {
  cava_arr :> Arrow;

  (* representable : object -> Type;
  constant {x} : representable x -> (unit ~> x); *)

  bit : object;
  fromBool : bool -> (unit ~> bit);

  not_gate : bit ~> bit;
  and_gate : (bit ** bit) ~> bit;
}.

Definition cava_cat (_: Cava): Category := _.
Definition cava_obj (cava: Cava): Type := @object (@cava_cat cava).

Definition high {_: Cava}: unit ~> bit := fromBool true.
Definition low {_: Cava}: unit ~> bit := fromBool false.

(* Delay as a different type class to allow implementing subset of primitives *)
Class CavaDelay := {
  delay_cava :> Cava;
  delay_gate {x} : x ~> x;
}.

Definition cava_delay_arr (_: CavaDelay): Arrow := _.

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
