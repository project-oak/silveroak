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

  (* fill an shape with a incremental numbering corresponding to new ports *)
  Fixpoint numberShape (s: shape) (i:N) : (signalTy N s * N) :=
  match s in shape return (signalTy N s * N) with
  | Empty => (tt, i)
  | Bit => (i, (i+1)%N)
  | BitVec n => (Vector.map N.of_nat (vec_seq (N.to_nat i) n), (i + N.of_nat n)%N)
  | Tuple2 t1 t2 =>
    let (x,i') := numberShape t1 i in
    let (y,i'') := numberShape t2 i' in
    ((x, y), i'')
  end.

  Local Open Scope monad_scope.
  Local Open Scope vector_scope.

  Instance NetlistCat : Category := {
    object := shape;
    morphism X Y := signalTy N X -> state (Netlist * N) (signalTy N Y);
    id X x := ret x;
    compose X Y Z f g := g >=> f;
  }.

  Instance NetlistArr : Arrow := {
    cat := NetlistCat;
    unit := Empty;
    product := Tuple2;

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

    bit := Bit;
    bitvec := BitVec;

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
      put (cons (BindNot x i) nl, (i+1)%N) ;;
      ret i;

    and_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (cons (BindAnd [x;y] i) nl, (i+1)%N) ;;
      ret i;

    nand_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (cons (BindNand [x;y] i) nl, (i+1)%N) ;;
      ret i;

    or_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (cons (BindOr [x;y] i) nl, (i+1)%N) ;;
      ret i;

    nor_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (cons (BindNor [x;y] i) nl, (i+1)%N) ;;
      ret i;

    xor_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (cons (BindXor [x;y] i) nl, (i+1)%N) ;;
      ret i;

    xnor_gate '(x,y) :=
      '(nl, i) <- get ;;
      put (cons (BindXnor [x;y] i) nl, (i+1)%N) ;;
      ret i;

    buf_gate x :=
      '(nl, i) <- get ;;
      put (cons (BindBuf x i) nl, (i+1)%N) ;;
      ret i;

    xorcy x :=
      '(nl, i) <- get ;;
      put (cons (BindXorcy x i) nl, (i+1)%N) ;;
      ret i;

    muxcy x :=
      '(nl, i) <- get ;;
      put (cons (BindMuxcy x i) nl, (i+1)%N) ;;
      ret i;

    unsigned_add m n s x :=
      '(nl, i) <- get ;;
      let o := Vector.map N.of_nat (vec_seq (N.to_nat i) s) in
      put (cons (BindUnsignedAdd x o) nl, (i + N.of_nat s)%N) ;;
      ret o;
  }.

  Local Close Scope vector_scope.

  (* The key here is that the dependent match needs to be over
    shape and ports p1 p2, at the same time for Coq to recogonise their types
    in the respective branches *)
  Fixpoint zipThenFlatten
    (link: N -> N -> PrimitiveInstance) (s: shape) (p1 p2: signalTy N s)
    : Netlist :=
  match s in shape, p1, p2 return Netlist with
  | Empty, _, _ => []
  | Bit, _, _ => [link p1 p2]
  | BitVec n, _, _ => Vector.to_list (Vector.map2 link p1 p2)
  | Tuple2 s1 s2, (p11,p12), (p21,p22) =>
      zipThenFlatten link s1 p11 p21 ++ zipThenFlatten link s2 p12 p22
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
      let links := zipThenFlatten BindAssignBit N n n' in
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
      let links := zipThenFlatten BindAssignBit N n n' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;
  }.

  Instance NetlistCavaDelay : CavaDelay := {
    delay_cava := NetlistCava;

    delay_gate X x :=
      '(nl, i) <- get ;;
      let '(x', i') := @numberShape X i in
      let links := zipThenFlatten BindDelayBit X x x' in
      put (links ++ nl, i') ;;
      ret x'
  }.

  Definition arrowToHDLModule {X Y}
    (name: string)
    (f: X ~[NetlistCat]~> Y)
    (mkInputs: signalTy N X -> list PortDeclaration)
    (mkOutputs: signalTy N Y -> list PortDeclaration)
    : (Netlist.Module * N) :=
      let (i, n) := @numberShape X 2 in
      let '(o, (nl, count)) := runState (f i) ([], n) in
      (mkModule name nl (mkInputs i) (mkOutputs o), count).

  (* Check ArrowExamples.v for xor example *)
  Eval cbv in arrowToHDLModule
    "not"
    not_gate
    (fun i => [mkPort "input1" Bit i])
    (fun o => [mkPort "output1" Bit o]).

End ArrowNetlist.