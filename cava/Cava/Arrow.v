Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq Require Import btauto.Btauto.

Generalizable All Variables.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "**" (at level 40, left associativity).
Reserved Infix ">>>" (at level 90, right associativity).

(** haskell-ish style category
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
Notation "g >>> f" := (compose f g)
  (at level 90, right associativity) : category_scope.

Open Scope category_scope.
Print Category.

(** adam megacz style arrow *)
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

Definition first `{Arrow} {x y z} (f : x ~> y) : x ** z ~> y ** z :=
  fork (exl >>> f) exr.

Definition second `{Arrow} {x y z} (f : x ~> y) : z ** x ~> z ** y :=
  fork exl (exr >>> f).

(** different type class for implementation to select features*)
Class ArrowLoop `{Arrow} := {
  loopr {x y z} : ((x**z) ~> (y**z)) -> (x ~> y);
  loopl {x y z} : ((z**x) ~> (z**y)) -> (x ~> y);
}.

Print Arrow.

(** Cava *)
Class Cava  := {
  cava_arrow :> Arrow;
  bit : object;

  fromBool : bool -> (unit ~> bit);

  not_gate : bit ~> bit;
  and_gate : (bit ** bit) ~> bit;
}.

Definition cava_cat (cava: Cava): Category := @cat (@cava_arrow cava).
Definition cava_obj (cava: Cava): Type := @object (@cava_cat cava).

Section highlow.
  Context `{Cava}.
  Definition high : unit ~> bit := fromBool true.
  Definition low : unit ~> bit := fromBool false.
End highlow.

(** different type class for implementation to select features*)
Class CavaDelay `{Cava} := {
  delay_gate {x} : x ~> x;
}.

(** Evaluation as function, no delay elements or loops *)
Section CoqEval.
  Instance CoqCat : Category := {
    morphism X Y := X -> Y;
    compose _ _ _ := fun f g x => f (g x);
    id X := fun x => x;
  }.

  Instance CoqArr : Arrow := {
    unit := Datatypes.unit : Type;
    product := prod;

    fork _ _ _ f g := fun x => (f x, g x);
    exl X Y := fst;
    exr X Y := snd;

    drop _ := fun x => tt;
    copy _ := fun x => pair x x;

    swap _ _ := fun x => (snd x, fst x);

    uncancell _ := fun x => (tt, x);
    uncancelr _ := fun x => (x, tt);

    assoc _ _ _   := fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz));
    unassoc _ _ _ := fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz));
  }.

  Instance CoqCava : Cava := {
    bit := bool;

    fromBool b := fun _ => b;

    not_gate := fun b => negb b;
    and_gate := fun xy => andb (fst xy) (snd xy);
  }.

  Context `{CavaCoq}.
  Eval cbv in not_gate true.
  Eval cbv in not_gate false.
End CoqEval.

(** Evaluation as function on lists, no loops, can't represent fromBool *)
(* Section CoqListEval.
  Instance CoqListCat : Category := {
    morphism X Y := list X -> list Y;
    compose _ _ _ := fun f g x => f (g x);
    id X := fun x => x;
  }.

  Instance CoqListArr : Arrow := {
    unit := Datatypes.unit : Type;

    fork _ _ _ f g := fun xs => combine (f xs) (g xs);
    exl X Y := map fst;
    exr X Y := map snd;

    drop _ := map (fun _ => tt);
    copy _ := map (fun x => pair x x);

    swap _ _ := map (fun x => (snd x, fst x));

    uncancell _ := map (fun x => (tt, x));
    uncancelr _ := map (fun x => (x, tt));

    assoc _ _ _   := map (fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)));
    unassoc _ _ _ := map (fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)));
  }.

  Instance CoqListCava : Cava := {
    bit := bool;

    (* fromBool b := fun _ => b; *)

    not_gate := map (fun b => negb b);
    and_gate := map (fun xy => andb (fst xy) (snd xy));
  }.
   
  Definition evalList (A: @object CoqListCat) (B: @object CoqListCat) (f: @morphism CoqListCat A B) (a:list A): list B := f a.

  Import ListNotations.

  Eval cbv in evalList not_gate [true;true;true].
  Eval cbv in evalList not_gate [false;false;false].
End CoqListEval. *)