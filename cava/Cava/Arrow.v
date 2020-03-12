Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

From Coq Require Import ZArith.
From Coq Require Import btauto.Btauto.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadFix.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Export ExtLib.Data.Monads.StateMonad.
Import MonadNotation.

Require Import Cava.Netlist.

Generalizable All Variables.

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

(* Evaluation as a netlist *)
Section ArrowNetlist.
  Inductive Shape :=
  | ShapeUnit: Shape
  | ShapeOne: Shape
  | ShapeProd: Shape -> Shape -> Shape.

  Fixpoint PortsOfShape (s: Shape): Type :=
  match s with
  | ShapeUnit => Datatypes.unit
  | ShapeOne => Z
  | ShapeProd t1 t2 => (PortsOfShape t1 * PortsOfShape t2)
  end.

  Fixpoint FillShape (s: Shape) (i:Z) : (PortsOfShape s * Z) :=
  match s in Shape return (PortsOfShape s * Z) with
  | ShapeUnit => (tt, i)
  | ShapeOne => (i, (i+1)%Z)
  | ShapeProd t1 t2 =>
    let (x,i') := FillShape t1 i in
    let (y,i'') := FillShape t2 i' in
    ((x, y), i'')
  end.

  Local Open Scope monad_scope.

  Instance NetlistCat : Category := {
    object := Shape;
    morphism X Y := PortsOfShape X -> state (Netlist * Z) (PortsOfShape Y);
    id X x := ret x;
    compose X Y Z f g := g >=> f;
  }.

  Instance NetlistArr : Arrow := {
    cat := NetlistCat;
    unit := ShapeUnit;
    product := ShapeProd;

    fork X Y Z f g z := 
      x <- f z ;;
      y <- g z ;;
      ret (x, y);

    exl X Y '(x,y) := ret x;
    exr X Y '(x,y) := ret y;


    drop _ _ := ret Datatypes.tt;
    copy _ x := ret (x,x);
    swap _ _ '(x,y) := ret (y,x);


    uncancell _ x := ret (tt, x);
    uncancelr _ x := ret (x, tt);

    assoc _ _ _ '((x,y),z) := ret (x,(y,z));
    unassoc _ _ _ '(x,(y,z)) := ret ((x,y),z);
  }.

  Instance NetlistCava : Cava := {
    cava_arr := NetlistArr;

    bit := ShapeOne;

    fromBool b := match b with
      | true => fun _ => ret 1%Z
      | false => fun _ => ret 0%Z
      end;

    not_gate x := 
      '(nl, i) <- get ;;
      put (Not x i :: nl, (i+1)%Z) ;;
      ret i;

    and_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (And [x;y] i :: nl, (i+1)%Z) ;;
      ret i;
  }.

  (* The key here is that the dependent match needs to be over 
    Shape and ports p1 p2, at the same time for Coq to recogonise their types
    in the respective branches *)
  Fixpoint linkWith (link: Z -> Z -> Primitive) (s: Shape) (p1 p2: PortsOfShape s) : Netlist :=
  match s in Shape, p1, p2 return Netlist with 
  | ShapeUnit, _, _ => []
  | ShapeOne, _, _ => [link p1 p2]
  | ShapeProd s1 s2, (p11,p12), (p21,p22) => linkWith link s1 p11 p21 ++ linkWith link s2 p12 p22
  end.

  Instance NetlistLoop : ArrowLoop NetlistArr := {
    (* 1. reserve (@FillShape Z _) items
       2. Run f with reserved items
       3. link the items and add the netlist *)
    loopr _ _ Z f x :=
      (* 1 *)
      '(nl, i) <- get ;;
      let '(z, i') := @FillShape Z i in
      put (nl, i') ;;

      (* 2 *)
      '(y,z') <- f (x,z) ;;

      (* 3 *)
      let links := linkWith AssignBit Z z z' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;

    loopl _ _ Z f x :=
      (* 1 *)
      '(nl, i) <- get ;;
      let '(z, i') := @FillShape Z i in
      put (nl, i') ;;

      (* 2 *)
      '(z', y) <- f (z, x) ;;

      (* 3 *)
      let links := linkWith AssignBit Z z z' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;

  }.

  Instance NetlistCavaDelay : CavaDelay := {
    delay_cava := NetlistCava;
    (* delay_gate {x} : x ~> x; *)
    delay_gate X x :=
      '(nl, i) <- get ;;
      let '(x', i') := @FillShape X i in
      let links := linkWith DelayBit X x x' in
      put (links ++ nl, i) ;;
      ret x'
  }.

  Definition arrowToHDLModule {X Y}
    (name: string)
    (f: X ~[NetlistCat]~> Y)
    (mkInputs: PortsOfShape X -> list PortDeclaration)
    (mkOutputs: PortsOfShape Y -> list PortDeclaration)
    : (Netlist.Module * Z) :=
      let (i, n) := @FillShape X 2 in
      let '(o, (nl, count)) := runState (f i) ([], n) in
      (mkModule name nl (mkInputs i) (mkOutputs o), count).

  (* Check ArrowExamples.v for xor example *)
  Eval cbv in arrowToHDLModule
    "not"
    not_gate
    (fun i => [mkPort "input1" (BitPort i)])
    (fun o => [mkPort "output1" (BitPort o)])
    .

End ArrowNetlist.
