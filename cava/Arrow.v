(* Require Coq.Program.Tactics. *)

Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.

From Coq Require Import btauto.Btauto.

Set Implicit Arguments.
Set Strict Implicit.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Set Typeclasses Debug.
Set Typeclasses Debug Verbosity 2.

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

Bind Scope category_scope with Category.
Delimit Scope category_scope with category.

Notation "x ~> y" := (morphism x y)
  (at level 90, right associativity) : category_scope.
Notation "g >>> f" := (compose f g)
  (at level 90, right associativity) : category_scope.


Open Scope category_scope.
Print Category.

(** adam megacz style arrow *)
Class Arrow (C: Category) := {
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
Class ArrowLoop {C: Category} (A: Arrow C) := {
  loopr {x y z} : ((x**z) ~> (y**z)) -> (x ~> y);
  loopl {x y z} : ((z**x) ~> (z**y)) -> (x ~> y);
}.

Print Arrow.

(** Cava *)
Class Cava (C: Category) (A: Arrow C) := {
  bit : object;
  fromBool : bool -> (unit ~> bit);

  not_gate : bit ~> bit;
  and_gate : (bit ** bit) ~> bit;
}.

Section highlow.
  Context `{Cava}.
  Definition high : unit ~> bit := fromBool true.
  Definition low : unit ~> bit := fromBool false.
End highlow.

(** different type class for implementation to select features*)
Class CavaDelay `{Cava} := {
  delay_gate : bit ~> bit;
}.

Print Cava.

(** Evaluation as function, no delay elements or loops *)
Section CoqEval.
  Instance CoqCat : Category := {
    morphism X Y := X -> Y;
    compose _ _ _ := fun f g x => f (g x);
    id X := fun x => x;
  }.

  Instance CoqArr : @Arrow CoqCat := {
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

  Instance CoqCava : @Cava CoqCat CoqArr := {
    bit := bool;

    fromBool b := fun _ => b;

    not_gate := fun b => negb b;
    and_gate := fun xy => andb (fst xy) (snd xy);
  }.

  Definition eval {A B} (f: A~>B) (a:A): B := f a.
  Definition eval' {B} (f: unit~>B) : B := f tt.

  Eval cbv in eval not_gate true.
  Eval cbv in eval not_gate false.
End CoqEval.


Section Example1.
  (* Context `{Cava }. *) (** not general enough?*)

  Definition nand
    {C: Category} {A: Arrow C}
    {Cava: @Cava C A}
    := and_gate >>> not_gate.

  Definition xor
    {C: Category} {A: Arrow C}
    {Cava: @Cava C A}
    : (bit**bit) ~> bit :=
    copy
    >>> first (nand >>> copy)      (* ((nand,nand),(x,y)) *)
    >>> assoc                      (* (nand,(nand,(x,y))) *)
    >>> second (unassoc >>> first nand >>> swap) (* (nand,(y, x_nand)) *)
    >>> unassoc >>> first nand          (* (y_nand,x_nand) *)
    >>> nand.

  Definition twoBits
    {C: Category} {A: Arrow C}
    {Cava: @Cava C A}
    : unit ~> (bit**bit) :=
    copy
    >>> first (fromBool true)
    >>> second (fromBool false).

  Existing Instance CoqArr.
  Existing Instance CoqCava.

  Print xor.
  Eval simpl in eval' (twoBits >>> and_gate).
  Eval cbv in eval' (twoBits >>> and_gate).
  Eval simpl in eval' (twoBits >>> nand).
  Eval cbv in eval' (twoBits >>> nand).
  Eval simpl in eval' (twoBits >>> xor).
  Eval cbv in eval' (twoBits >>> xor).

  Definition twoBools
    {C: Category} {A: Arrow C}
    {Cava: @Cava C A}
    (x y: bool): unit ~> (bit**bit) :=
    copy
    >>> first (fromBool x)
    >>> second (fromBool y).

  (** *)
  Lemma xor_is_xorb : forall a b:bool, eval' (twoBools a b >>> xor) = xorb a b.
  Proof.
    intros.
    unfold eval'.
    simpl.
    btauto.
  Qed.

End Example1.

Section Example2.
  (*nand previous output and current input, output delayed 1 cycle*)
  Definition loopedNand
    {C: Category}
    {A: Arrow C} {AL: ArrowLoop A}
    {Cava: @Cava C A}
    `{@CavaDelay C A Cava}
    : bit ~> bit :=
    loopl (nand >>> delay_gate >>> copy).
End Example2.
