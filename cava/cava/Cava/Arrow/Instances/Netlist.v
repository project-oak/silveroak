From Coq Require Import Program.Tactics.
From Coq Require Import Bool.Bool.
(* From Coq Require Import Bool.Bvector. *)
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

(******************************************************************************)
(* Evaluation as a netlist                                                    *)
(******************************************************************************)

Section NetlistEval.
  Local Open Scope monad_scope.

  Instance NetlistCat : Category := {
    object := @shape portType;
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

    bit := One Bit;
    bitvec n := One (BitVec [n]);

    constant b _ := match b with
      | true => ret 1%N
      | false => ret 0%N
      end;

    constant_vec n v _ := ret (Vector.to_list (Vector.map (fun b => match b with
      | true => 1%N
      | false => 0%N
    end) v));

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
      let o := map N.of_nat (seq (N.to_nat i) s) in
      put (cons (BindUnsignedAdd s x o) nl, (i + N.of_nat s)%N) ;;
      ret o;
  }.

  Fixpoint map2WithPortShape {A B C} (f: A -> B -> C) (port: portType)
    (x: portTypeTy A port) (y: portTypeTy B port): portTypeTy C port :=
    match port in portType, x, y return  portTypeTy C port with
    | Bit, x, y => f x y
    | BitVec sz, xs, ys => mapBitVec (fun '(x,y) => f x y) sz sz (zipBitVecs sz sz xs ys)
    end .

  Fixpoint linkShapes {A B}
     (link: A -> B -> PrimitiveInstance) (s: shape)
     (p1: signalTy A s)
     (p2: signalTy B s)
     : Netlist :=
    match s in shape, p1, p2 with
    | Empty, _, _ => []
    | One a, _, _ => flattenPort a (map2WithPortShape link a p1 p2)
    | Tuple2 s1 s2, (p11,p12), (p21,p22) => (linkShapes link s1 p11 p21) ++
        (linkShapes link s2 p12 p22)
    end.

  Definition bitsInPortShape' i s := (i + N.of_nat (bitsInPortShape s))%N.

  Instance NetlistLoop : ArrowLoop NetlistArr := {
    (* 1. reserve (@numberShape N _) items
       2. Run f with reserved items
       3. link the items and add the netlist *)
    loopr _ _ N f x :=
      (* 1 *)
      '(nl, i) <- get ;;
      let n := numberPort i N in
      let i' := bitsInPortShape' i N in
      put (nl, i') ;;

      (* 2 *)
      '(y,n') <- f (x,n) ;;

      (* 3 *)
      let links := linkShapes BindAssignBit N n n' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;

    loopl _ _ N f x :=
      (* 1 *)
      '(nl, i) <- get ;;
      let n := numberPort i N in
      let i' := bitsInPortShape' i N in
      put (nl, i') ;;

      (* 2 *)
      '(n', y) <- f (n, x) ;;

      (* 3 *)
      let links := linkShapes BindAssignBit N n n' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;
  }.

  Instance NetlistCavaDelay : CavaDelay := {
    delay_cava := NetlistCava;

    delay_gate X x :=
      '(nl, i) <- get ;;
      let x' := numberPort i X in
      let i' := bitsInPortShape' i X in
      let links := linkShapes BindDelayBit X x x' in
      put (links ++ nl, i') ;;
      ret x'
  }.

  Definition wireInput (port_shape: portType) (name: string) (port: portTypeTy N port_shape)
    : PrimitiveInstance :=
    match port_shape, port with
    | Bit,_ => BindPrimitive (WireInputBit name) tt port
    | BitVec sz,_ => BindPrimitive (WireInputBitVec name) tt port
    end.

  Definition wireOutput (port_shape: portType) (name: string) (port: portTypeTy N port_shape)
    : PrimitiveInstance :=
    match port_shape, port with
    | Bit,_ => BindPrimitive (WireOutputBit name) port tt
    | BitVec sz,_ => BindPrimitive (WireOutputBitVec name) port tt
    end.

  Fixpoint nameTy {A} (s : @shape A) : Type :=
    match s with
    | Empty  => Datatypes.unit
    | One t => string
    | Tuple2 s1 s2  => prod (nameTy s1) (nameTy s2)
    end.

  Fixpoint linkLables {A}
     (link: forall port_shape, string -> portTypeTy N port_shape -> A)
     (s: shape)
     (labels: nameTy s)
     (ports: signalTy N s)
     : list A :=
    match s in shape, labels, ports with
    | Empty, _, _ => []
    | One port_shape, name, port => [link port_shape name port]
    | Tuple2 s1 s2, (l1,l2), (p1,p2) => (linkLables link s1 l1 p1) ++ (linkLables link s2 l2 p2)
    end.

  Fixpoint namePorts
     (s: @shape portType)
     (labels: nameTy s)
     : list PortDeclaration :=
    match s in shape, labels with
    | Empty, _ => []
    | One port_shape, name => [mkPort name port_shape]
    | Tuple2 s1 s2, (l1,l2) => (namePorts s1 l1) ++ (namePorts s2 l2)
    end.

  Definition nameInputs {X}
    (input_names: nameTy X)
    : X ~[NetlistCat]~> X :=
      fun x =>
        '(nl, i) <- get ;;
        let links := linkLables wireInput X input_names x in
        put (links ++ nl, i) ;;
        ret x.

  Definition nameOutputs {X}
    (output_names: nameTy X)
    : X ~[NetlistCat]~> X :=
      fun x =>
        '(nl, i) <- get ;;
        let links := linkLables wireOutput X output_names x in
        put (links ++ nl, i) ;;
        ret x.

  Definition arrowToHDLModule {X Y}
    (name: string)
    (f: X ~[NetlistCat]~> Y)
    (input_names: nameTy X)
    (output_names: nameTy Y)
    : Netlist.CavaState :=
      let i := numberPort 2 X in
      let n := bitsInPortShape' 2 X in
      let '(o, (netlist, count)) := runState ((nameInputs input_names >=> f >=> nameOutputs output_names) i) ([], n) in
      let module_inputs := namePorts X input_names in
      let module_ouputs := namePorts Y output_names in
      let module := mkModule name netlist module_inputs module_ouputs in
      mkCavaState count true module.

  (* Check ArrowExamples.v for xor example *)
  Local Open Scope string_scope.
  Eval cbv in arrowToHDLModule
    "not"
    not_gate
    ("input1")
    ("output1").

End NetlistEval.
