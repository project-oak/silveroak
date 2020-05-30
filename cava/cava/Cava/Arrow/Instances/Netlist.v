From Coq Require Import Program.Tactics.
From Coq Require Import Bool.Bool.
From Coq Require Import Vector.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import Numbers.DecimalString.
From Coq Require Import Bool.Bvector.

Import NilZero.

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
    morphism X Y := signalTy Signal X -> state CavaState (signalTy Signal Y);
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

  Fixpoint object_as_list n:
    forall x, signalTy Signal (replicate_object n (One x)) -> list (signalTy Signal (One x)).
  Proof.
    intros.

    induction n.
    simpl in *.
    exact ([]).

    simpl in *.
    refine (fst X :: _).
    apply (IHn (snd X)).
  Defined.

  Fixpoint bv_to_nprod n (v: Bvector n): NaryFunctions.nprod bool n.
  Proof.
    unfold Bvector in *.
    destruct n.
    exact tt.
    refine (pair _ _ ).
    exact (Vector.hd v).
    exact (bv_to_nprod n (Vector.tl v)).
  Defined.

  #[refine] Instance NetlistCava : Cava := {
    cava_arrow := NetlistArr;

    representable ty := match ty with
    | Bit => One Bit
    | BitVec xs => One (BitVec xs)
    | ExternalType t => One (ExternalType t)
    end;

    constant b _ := match b with
      | true => ret Vcc
      | false => ret Gnd
      end;

    constant_vec n v _ := ret (mapBitVec (fun b => match b with
      | true => Vcc
      | false => Gnd
    end) n n v);

    not_gate '(i,tt) :=
      o <- newWire ;;
      addInstance (Not i o) ;;
      ret o;

    and_gate '(i0,(i1,tt)) :=
      o <- newWire ;;
      addInstance (And i0 i1 o) ;;
      ret o;

    nand_gate '(i0,(i1,tt)) :=
      o <- newWire ;;
      addInstance (Nand i0 i1 o) ;;
      ret o;

    or_gate '(i0,(i1,tt)) :=
      o <- newWire ;;
      addInstance (Or i0 i1 o) ;;
      ret o;

    nor_gate '(i0,(i1,tt)) :=
      o <- newWire ;;
      addInstance (Nor i0 i1 o) ;;
      ret o;

    xor_gate '(i0,(i1,tt)) :=
      o <- newWire ;;
      addInstance (Xor i0 i1 o) ;;
      ret o;

    xnor_gate '(i0,(i1,tt)) :=
      o <- newWire ;;
      addInstance (Xnor i0 i1 o) ;;
      ret o;

    buf_gate '(i,tt) :=
      o <- newWire ;;
      addInstance (Buf i o) ;;
      ret o;

    xorcy '(i0, (i1, tt)) :=
      o <- newWire ;;
      addInstance (Component "XORCY" [] [("O", o); ("CI", i0); ("LI", i1)]) ;;
      ret o;

    muxcy '(s,((ci, di), tt)) :=
      o <- newWire ;;
      addInstance ( Component "MUXCY" [] [("O", o); ("S", s); ("CI", ci); ("DI", di)]) ;;
      ret o;

    unsigned_add m n s '(x,(y, tt)) :=
      sum <- newWires s ;;
      addInstance (UnsignedAdd x y sum) ;;
      ret sum;

    lut n f is :=
      let seq := seq 0 (2^n) in
      let f' := NaryFunctions.nuncurry bool bool n f in 
      let powers := map
        (fun p => let bv := Ndigits.N2Bv_sized n (N.of_nat p) in
                  2^(N.of_nat p) * N.b2n (f' (bv_to_nprod n bv))
        )%N
        seq in
      let config := fold_left N.add powers 0%N in
      let component_name := ("LUT" ++ string_of_uint (Nat.to_uint n))%string in
      let is_as_list := object_as_list n _ is in
      let inputs := map 
        (fun '(i, n) => ("I" ++ string_of_uint (Nat.to_uint i), n))%string 
        (combine seq is_as_list) in
      o <- newWire ;;
      let component := 
        Component
        component_name [("INIT", HexLiteral (2^n) config)]
        (("O", o) :: inputs) in
      addInstance component;;
      ret o;
    
    index_array x xs '(array, (index, _)) := 
      o <- newWiresBitVec xs;;
      addInstance (IndexAlt x xs array index o) ;;
      ret _; 
      
    to_vec n o := _;
  }.
  Proof.
    - destruct xs; simpl in *; exact (o). 
    - intros.
      destruct o. 
      * cbv [cat NetlistArr NetlistCat morphism].
        intros.
        apply object_as_list in X.
        exact (ret X).
      * cbv [cat NetlistArr NetlistCat morphism].
        intros.
        apply object_as_list in X.
        simpl in *.
        destruct l; exact (ret X).
      * cbv [cat NetlistArr NetlistCat morphism].
        intros.
        apply object_as_list in X.
        exact (ret X).
  Defined.

  Close Scope string_scope.

  Fixpoint map2WithPortShape {A B C} (f: A -> B -> C) (port: Kind)
    (x: denoteKindWith port A) (y: denoteKindWith port B): denoteKindWith port C :=
    match port in Kind, x, y return denoteKindWith port C with
    | Bit, x, y => f x y
    | BitVec sz, xs, ys => mapBitVec (fun '(x,y) => f x y) sz sz (zipBitVecs sz sz xs ys)
    | ExternalType t, x, y => f x y
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

  Instance NetlistLoop : ArrowLoop NetlistArr := {
    loopr _ _ Z f x :=
      z <- newWiresFromShape Z ;;
      '(y,z') <- f (x,z) ;;
      let links := linkShapes AssignBit Z z z' in
      addSequentialInstances links;;
      ret y;

    loopl _ _ Z f x :=
      z <- newWiresFromShape Z ;;
      '(z',y) <- f (z,x) ;;
      let links := linkShapes AssignBit Z z z' in
      addSequentialInstances links;;
      ret y;
  }.

  Instance NetlistCavaDelay : CavaDelay := {
    delay_cava := NetlistCava;

    delay_gate X '(x,tt) :=
      y <- newWiresFromShape X ;;
      let links := linkShapes DelayBit X x y in
      addSequentialInstances links;;
      ret y;
  }.

End NetlistEval.