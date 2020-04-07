From Coq Require Import Program.Tactics.
From Coq Require Import Bool.Bool.
From Coq Require Import Bool.Bvector.
From Coq Require Import Vector.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Import ListNotations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadFix.
From ExtLib Require Export Data.Monads.IdentityMonad.
From ExtLib Require Export Data.Monads.StateMonad.

Import MonadNotation.

From Cava Require Import Netlist.
From Cava Require Import BitArithmetic.
From Cava Require Import Arrow.Arrow.

(* Evaluation as a netlist *)
Section ArrowNetlist.
  Inductive ArrowShape :=
  | AZero: ArrowShape
  | AOne: ArrowShape
  | AVec: nat -> ArrowShape
  | AProd: ArrowShape -> ArrowShape -> ArrowShape.

  (* convert an ArrowShape to a Coq Type *)
  Fixpoint shapeToCoq (s: ArrowShape): Type :=
  match s with
  | AZero => Datatypes.unit
  | AOne => N
  | AVec n => Vector.t N n
  | AProd t1 t2 => (shapeToCoq t1 * shapeToCoq t2)
  end.

  (* fill an ArrowShape with a incremental numbering corresponding to new ports *)
  Fixpoint numberShape (s: ArrowShape) (i:N) : (shapeToCoq s * N) :=
  match s in ArrowShape return (shapeToCoq s * N) with
  | AZero => (tt, i)
  | AOne => (i, (i+1)%N)
  | AVec n =>
      (Vector.map N.of_nat (vec_seq (N.to_nat i) n), (i + N.of_nat n)%N)
  | AProd t1 t2 =>
    let (x,i') := numberShape t1 i in
    let (y,i'') := numberShape t2 i' in
    ((x, y), i'')
  end.

  Local Open Scope monad_scope.

  Instance NetlistCat : Category := {
    object := ArrowShape;
    morphism X Y := shapeToCoq X -> state (Netlist * N) (shapeToCoq Y);
    id X x := ret x;
    compose X Y Z f g := g >=> f;
  }.

  Instance NetlistArr : Arrow := {
    cat := NetlistCat;
    unit := AZero;
    product := AProd;

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

    bit := AOne;
    bitvec := AVec;

    constant b _ := match b with
      | true => ret 1%N
      | false => ret 0%N
      end;

    constant_vec n v _ := ret (Vector.map (fun b => match b with
      | true => 1%N
      | false => 0%N
    end) v);

    not_gate x :=
      '(nl, i) <- get ;;
      put (Not x i :: nl, (i+1)%N) ;;
      ret i;

    and_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (And [x;y] i :: nl, (i+1)%N) ;;
      ret i;

    nand_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (Nand [x;y] i :: nl, (i+1)%N) ;;
      ret i;

    or_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (Or [x;y] i :: nl, (i+1)%N) ;;
      ret i;

    nor_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (Nor [x;y] i :: nl, (i+1)%N) ;;
      ret i;

    xor_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (Xor [x;y] i :: nl, (i+1)%N) ;;
      ret i;

    xnor_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (Xnor [x;y] i :: nl, (i+1)%N) ;;
      ret i;

    buf_gate x :=
      '(nl, i) <- get ;;
      put (Buf x i :: nl, (i+1)%N) ;;
      ret i;

    xorcy '(x,y) :=
      '(nl, i) <- get ;;
      put (Xorcy x y i :: nl, (i+1)%N) ;;
      ret i;

    muxcy '(ii,t,e) :=
      '(nl, i) <- get ;;
      put (Muxcy ii t e i :: nl, (i+1)%N) ;;
      ret i;

    unsigned_add m n s '(a,b) :=
      '(nl, i) <- get ;;
      let o := Vector.map N.of_nat (vec_seq (N.to_nat i) s) in
      put (UnsignedAdd m n s a b o :: nl, (i + N.of_nat s)%N) ;;
      ret o;
  }.

  (* The key here is that the dependent match needs to be over
    ArrowShape and ports p1 p2, at the same time for Coq to recogonise their types
    in the respective branches *)
  Fixpoint zipThenFlatten (link: N -> N -> Primitive) (s: ArrowShape) (p1 p2: shapeToCoq s) : Netlist :=
  match s in ArrowShape, p1, p2 return Netlist with
  | AZero, _, _ => []
  | AOne, _, _ => [link p1 p2]
  | AVec n, _, _ => Vector.to_list (Vector.map2 link p1 p2)
  | AProd s1 s2, (p11,p12), (p21,p22) => zipThenFlatten link s1 p11 p21 ++ zipThenFlatten link s2 p12 p22
  end.

  Instance NetlistLoop : ArrowLoop NetlistArr := {
    (* 1. reserve (@numberShape N _) items
       2. Run f with reserved items
       3. link the items and add the netlist *)
    loopr _ _ N f x :=
      (* 1 *)
      '(nl, i) <- get ;;
      let '(n, i') := @numberShape N i in
      put (nl, i') ;;

      (* 2 *)
      '(y,n') <- f (x,n) ;;

      (* 3 *)
      let links := zipThenFlatten AssignBit N n n' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;

    loopl _ _ N f x :=
      (* 1 *)
      '(nl, i) <- get ;;
      let '(n, i') := @numberShape N i in
      put (nl, i') ;;

      (* 2 *)
      '(n', y) <- f (n, x) ;;

      (* 3 *)
      let links := zipThenFlatten AssignBit N n n' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;

  }.

  Instance NetlistCavaDelay : CavaDelay := {
    delay_cava := NetlistCava;

    delay_gate X x :=
      '(nl, i) <- get ;;
      let '(x', i') := @numberShape X i in
      let links := zipThenFlatten DelayBit X x x' in
      put (links ++ nl, i') ;;
      ret x'
  }.

  Definition arrowToHDLModule {X Y}
    (name: string)
    (f: X ~[NetlistCat]~> Y)
    (mkInputs: shapeToCoq X -> list PortDeclaration)
    (mkOutputs: shapeToCoq Y -> list PortDeclaration)
    : (Netlist.Module * N) :=
      let (i, n) := @numberShape X 2 in
      let '(o, (nl, count)) := runState (f i) ([], n) in
      (mkModule name nl (mkInputs i) (mkOutputs o), count).

  (* Check ArrowExamples.v for xor example *)
  Eval cbv in arrowToHDLModule
    "not"
    not_gate
    (fun i => [mkPort "input1" (BitPort i)])
    (fun o => [mkPort "output1" (BitPort o)]).

End ArrowNetlist.
