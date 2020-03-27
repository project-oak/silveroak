Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

From Coq Require Import ZArith.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadFix.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Export ExtLib.Data.Monads.StateMonad.
Import MonadNotation.

Require Import Cava.Netlist.
Require Import Cava.Arrow.Arrow.

(* Evaluation as a netlist *)
Section ArrowNetlist.
  Inductive Shape :=
  | ShapeUnit: Shape
  | ShapeOne: Shape
  | ShapeProd: Shape -> Shape -> Shape.

  Fixpoint PortsOfShape (s: Shape): Type :=
  match s with
  | ShapeUnit => Datatypes.unit
  | ShapeOne => N
  | ShapeProd t1 t2 => (PortsOfShape t1 * PortsOfShape t2)
  end.

  Fixpoint FillShape (s: Shape) (i:N) : (PortsOfShape s * N) :=
  match s in Shape return (PortsOfShape s * N) with
  | ShapeUnit => (tt, i)
  | ShapeOne => (i, (i+1)%N)
  | ShapeProd t1 t2 =>
    let (x,i') := FillShape t1 i in
    let (y,i'') := FillShape t2 i' in
    ((x, y), i'')
  end.

  Local Open Scope monad_scope.

  Instance NetlistCat : Category := {
    object := Shape;
    morphism X Y := PortsOfShape X -> state (Netlist * N) (PortsOfShape Y);
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
      | true => fun _ => ret 1%N
      | false => fun _ => ret 0%N
      end;

    not_gate x :=
      '(nl, i) <- get ;;
      put (Not x i :: nl, (i+1)%N) ;;
      ret i;

    and_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (And [x;y] i :: nl, (i+1)%N) ;;
      ret i;
  }.

  (* The key here is that the dependent match needs to be over
    Shape and ports p1 p2, at the same time for Coq to recogonise their types
    in the respective branches *)
  Fixpoint linkWith (link: N -> N -> Primitive) (s: Shape) (p1 p2: PortsOfShape s) : Netlist :=
  match s in Shape, p1, p2 return Netlist with
  | ShapeUnit, _, _ => []
  | ShapeOne, _, _ => [link p1 p2]
  | ShapeProd s1 s2, (p11,p12), (p21,p22) => linkWith link s1 p11 p21 ++ linkWith link s2 p12 p22
  end.

  Instance NetlistLoop : ArrowLoop NetlistArr := {
    (* 1. reserve (@FillShape N _) items
       2. Run f with reserved items
       3. link the items and add the netlist *)
    loopr _ _ N f x :=
      (* 1 *)
      '(nl, i) <- get ;;
      let '(n, i') := @FillShape N i in
      put (nl, i') ;;

      (* 2 *)
      '(y,n') <- f (x,n) ;;

      (* 3 *)
      let links := linkWith AssignBit N n n' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;

    loopl _ _ N f x :=
      (* 1 *)
      '(nl, i) <- get ;;
      let '(n, i') := @FillShape N i in
      put (nl, i') ;;

      (* 2 *)
      '(n', y) <- f (n, x) ;;

      (* 3 *)
      let links := linkWith AssignBit N n n' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;

  }.

  Instance NetlistCavaDelay : CavaDelay := {
    delay_cava := NetlistCava;

    delay_gate X x :=
      '(nl, i) <- get ;;
      let '(x', i') := @FillShape X i in
      let links := linkWith DelayBit X x x' in
      put (links ++ nl, i') ;;
      ret x'
  }.

  Definition arrowToHDLModule {X Y}
    (name: string)
    (f: X ~[NetlistCat]~> Y)
    (mkInputs: PortsOfShape X -> list PortDeclaration)
    (mkOutputs: PortsOfShape Y -> list PortDeclaration)
    : (Netlist.Module * N) :=
      let (i, n) := @FillShape X 2 in
      let '(o, (nl, count)) := runState (f i) ([], n) in
      (mkModule name nl (mkInputs i) (mkOutputs o), count).

  (* Check ArrowExamples.v for xor example *)
  Eval cbv in arrowToHDLModule
    "not"
    not_gate
    (fun i => [mkPort "input1" (BitPort i)])
    (fun o => [mkPort "output1" (BitPort o)]).

End ArrowNetlist.
