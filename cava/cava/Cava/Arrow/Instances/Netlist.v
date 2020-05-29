From Coq Require Import Program.Tactics.
From Coq Require Import Bool.Bool.
(* From Coq Require Import Bool.Bvector. *)
From Coq Require Import Vector.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Import ListNotations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.MonadLaws.
From ExtLib Require Import Structures.MonadFix.
From ExtLib Require Export Data.Monads.IdentityMonad.
From ExtLib Require Export Data.Monads.StateMonad.

Import MonadNotation.

From Cava Require Import Netlist.
From Cava Require Import Types.
From Cava Require Import Signal.
From Cava Require Import BitArithmetic.
From Cava Require Import Arrow.Arrow.

From Coq Require Import Setoid.
From Coq Require Import Classes.Morphisms.
Require Import FunctionalExtensionality.

(******************************************************************************)
(* Evaluation as a netlist                                                    *)
(******************************************************************************)

Section NetlistEval.
  Local Open Scope monad_scope.
  Local Open Scope string_scope.

  #[refine] Instance NetlistCat : Category := {
    object := bundle;
    morphism X Y := signalTy Signal X -> state (Netlist * N) (signalTy Signal Y);
    id X x := ret x;
    compose X Y Z f g := g >=> f;

    (* todo: add proper equivalence, netlist is equal modulo renumbering and intermediate state *)
    morphism_equivalence x y f g := True;
  }.
  Proof.
    intros.
    apply Build_Equivalence.
    unfold Reflexive. auto.
    unfold Symmetric. auto.
    unfold Transitive. auto.
    intros.
    unfold Proper.
    refine (fun f => _). intros.
    refine (fun g => _). intros.
    auto.

    auto. auto. auto.
  Defined.

  #[refine] Instance NetlistArr : Arrow := {
    cat := NetlistCat;
    unit := Empty;
    product := Tuple2;

    first X Y Z f '(z,y) :=
      x <- f z ;;
      ret (x,y);

    second X Y Z f '(y,z) :=
      x <- f z ;;
      ret (y,x);

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
  Proof.
    intros.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
    simpl; auto.
  Defined.

  Instance NetlistCava : Cava := {
    cava_arrow := NetlistArr;

    bit := One Bit;
    bitvec n := One (BitVec n);

    constant b _ := match b with
      | true => ret Vcc
      | false => ret Gnd
      end;

    constant_vec n v _ := ret (mapBitVec (fun b => match b with
      | true => Vcc
      | false => Gnd
    end) n n v);

    not_gate '(x,tt) :=
      '(nl, i) <- get ;;
      put (cons (Not x (Wire i)) nl, (i+1)%N) ;;
      ret (Wire i);

    and_gate '(x,(y,tt)) :=
      '(nl, i) <- get ;;
      put (cons (And x y (Wire i)) nl, (i+1)%N) ;;
      ret (Wire i);

    nand_gate '(x,(y,tt)) :=
      '(nl, i) <- get ;;
      put (cons (Nand x y (Wire i)) nl, (i+1)%N) ;;
      ret (Wire  i);

    or_gate '(x,(y,tt)) :=
      '(nl, i) <- get ;;
      put (cons (Or x y (Wire i)) nl, (i+1)%N) ;;
      ret (Wire i);

    nor_gate '(x,(y,tt)) :=
      '(nl, i) <- get ;;
      put (cons (Nor x y (Wire i)) nl, (i+1)%N) ;;
      ret (Wire i);

    xor_gate '(x,(y,tt)) :=
      '(nl, i) <- get ;;
      put (cons (Xor x y (Wire i)) nl, (i+1)%N) ;;
      ret (Wire i);

    xnor_gate '(x,(y,tt)) :=
      '(nl, i) <- get ;;
      put (cons (Xnor x y (Wire i)) nl, (i+1)%N) ;;
      ret (Wire i);

    buf_gate '(x,tt) :=
      '(nl, i) <- get ;;
      put (cons (Buf x (Wire i)) nl, (i+1)%N) ;;
      ret (Wire i);

    xorcy '(x, (y, tt)) :=
      '(nl, i) <- get ;;
      put (cons (Component "XORCY" [] [("O", Wire i); ("CI", x); ("LI", y)]) nl, (i+1)%N) ;;
      ret (Wire i);

    muxcy '(s,(ci,(di, tt))) :=
      '(nl, i) <- get ;;
      put (cons (Component "MUXCY" [] [("O", Wire i); ("S", s); ("CI", ci); ("DI", di)]) nl, (i+1)%N) ;;
      ret (Wire i);

    unsigned_add m n s '(x,(y, tt)) :=
      '(nl, i) <- get ;;
      let o := map N.of_nat (seq (N.to_nat i) s) in
      put (cons (UnsignedAdd x y (map Wire o)) nl, (i + N.of_nat s)%N) ;;
      ret (map Wire o);
  }.

  Close Scope string_scope.

  Fixpoint map2WithPortShape {A B C} (f: A -> B -> C) (port: Kind)
    (x: denoteKindWith port A) (y: denoteKindWith port B): denoteKindWith port C :=
    match port in Kind, x, y return  denoteKindWith port C with
    | Bit, x, y => f x y
    | BitVec sz, xs, ys => mapBitVec (fun '(x,y) => f x y) sz sz (zipBitVecs sz sz xs ys)
    end .

  Fixpoint linkShapes {A B}
     (link: A -> B -> Instance) (s: shape)
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
      let links := linkShapes AssignBit N n n' in
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
      let links := linkShapes AssignBit N n n' in
      '(nl, i) <- get ;;
      put (links ++ nl, i) ;;

      ret y;
  }.

  Instance NetlistCavaDelay : CavaDelay := {
    delay_cava := NetlistCava;

    delay_gate X '(x,tt) :=
      '(nl, i) <- get ;;
      let x' := numberPort i X in
      let i' := bitsInPortShape' i X in
      let links := linkShapes DelayBit X x x' in
      put (links ++ nl, i') ;;
      ret x'
  }.

  Definition wireInput (port_shape: Kind) (name: string) (port: denoteKindWith port_shape Signal)
    : Instance :=
    match port_shape, port with
    | Bit,_ => WireInputBit name port
    | BitVec sz,_ => WireInputBitVec sz name port
    end.

  Definition wireOutput (port_shape: Kind) (name: string) (port: denoteKindWith port_shape Signal)
    : Instance :=
    match port_shape, port with
    | Bit,_ => WireOutputBit name port
    | BitVec sz,_ => WireOutputBitVec sz name port
    end.

  Fixpoint nameTy {A} (s : @shape A) : Type :=
    match s with
    | Empty  => Datatypes.unit
    | One t => string
    | Tuple2 s1 s2  => prod (nameTy s1) (nameTy s2)
    end.

  Fixpoint linkLables {A}
     (link: forall port_shape, string -> denoteKindWith port_shape Signal -> A)
     (s: shape)
     (labels: nameTy s)
     (ports: signalTy Signal s)
     : list A :=
    match s in shape, labels, ports with
    | Empty, _, _ => []
    | One port_shape, name, port => [link port_shape name port]
    | Tuple2 s1 s2, (l1,l2), (p1,p2) => (linkLables link s1 l1 p1) ++ (linkLables link s2 l2 p2)
    end.

  Fixpoint namePorts
     (s: bundle)
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
    ("input1", tt)
    ("output1").

End NetlistEval.
