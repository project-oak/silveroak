From Coq Require Import Bool.Bvector.
From Coq Require Import Bool.Bool.

From Cava Require Import Netlist.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "**" (at level 30, right associativity).
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

  copy {x} : x ~> x**x;
  drop {x} : x ~> unit;
  swap {x y} : x**y ~> y**x;

  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y ** z;
  exl  {x y} : x ** y ~> x;
  exr  {x y} : x ** y ~> y;

  uncancell {x} : x ~> unit**x;
  uncancelr {x} : x ~> x**unit;
  assoc {x y z} : ((x**y)**z) ~> (x**(y**z));
  unassoc {x y z} : (x**(y**z)) ~> ((x**y)**z);
}.

Declare Scope arrow_scope.
Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (product x y)
  (at level 30, right associativity) : arrow_scope.

Open Scope arrow_scope.

Definition first {_: Arrow} {x y z} (f : x ~> y) : x ** z ~> y ** z :=
  fork (exl >>> f) exr.

Definition second {_: Arrow} {x y z} (f : x ~> y) : z ** x ~> z ** y :=
  fork exl (exr >>> f).

(* Loop as a different type class to allow implementating a subset of features *)
Class ArrowLoop (A: Arrow) := {
  loopr {x y z} : (x**z ~> y**z) -> (x ~> y);
  loopl {x y z} : (z**x ~> z**y) -> (x ~> y);
}.

Print Arrow.

(* Cava *)
Class Cava  := {
  cava_arr :> Arrow;

  bit : object;
  bitvec : nat -> object;

  constant : bool -> (unit ~> bit);
  constant_vec (n:nat) : Bvector n -> (unit ~> bitvec n);

  not_gate:  bit        ~> bit;
  and_gate:  bit ** bit ~> bit;
  nand_gate: bit ** bit ~> bit;
  or_gate:   bit ** bit ~> bit;
  nor_gate:  bit ** bit ~> bit;
  xor_gate:  bit ** bit ~> bit;
  xnor_gate: bit ** bit ~> bit;
  buf_gate:  bit        ~> bit;

  xorcy:     bit ** bit ~> bit;
  muxcy:     bit ** (bit ** bit) ~> bit;

  unsigned_add a b s: bitvec a ** bitvec b ~> bitvec s;
}.

Definition cava_cat (_: Cava): Category := _.
Definition cava_obj (cava: Cava): Type := @object (@cava_cat cava).

Definition high {_: Cava}: unit ~> bit := constant true.
Definition low {_: Cava}: unit ~> bit := constant false.

(* Delay as a different type class to allow implementing subset of primitives *)
Class CavaDelay := {
  delay_cava :> Cava;
  delay_gate {x} : x ~> x;
}.

Definition cava_delay_arr (_: CavaDelay): Arrow := _.
