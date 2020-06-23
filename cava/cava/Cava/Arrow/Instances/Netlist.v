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
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Traversable.
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

Fixpoint denote (ty: Kind): Type :=
match ty with
| Tuple l r => prod (denote l) (denote r)
| Unit => Datatypes.unit
| Bit => Signal
| Vector n t => Vector.t (denote t) n
end.

Section traversable.
  Universe u v vF.
  Context {F : Type@{v} -> Type@{vF}}.
  Context {Applicative_F : Applicative F}.
  Context {A : Type@{u}} {B : Type@{v}}.
  Variable f : A -> F B.

  Fixpoint mapT_vector@{} {n} (v : Vector.t A n ) : F (Vector.t B n).
  Proof.
    inversion v.
    exact (@pure F _ _ []%vector).
    refine (
        let _1 := fun y ys => @Vector.cons B y _ ys in
        let _2 := @pure F _ _ _1 in
        let _3 := @ap F _ _ _ _2 (f h) in
        let xs' := mapT_vector _ X in
        let _4 := @ap F _ _ _  _3 in
        _
    ).
    apply _4 in xs' .
    exact xs'.
  Defined.
End traversable.

Definition fixup n (F : Type -> Type) (Ap: Applicative F) (A B : Type) (m: A -> F B) := @mapT_vector F Ap A B m n.

Global Instance Traversable_vector@{} {n} : Traversable (fun t => Vector.t t n) :=
{ mapT := fixup n }.

Fixpoint build (ty: Kind) : state CavaState (denote ty) :=
match ty with
| Tuple l r =>
  l <- build l;;
  r <- build r;;
  ret (l, r)
| Unit => ret tt
| Bit => newWire
| Vector n t => mapT (fun _ => build t) (const tt n)
end.

Fixpoint mapMSignals2 (f: Signal -> Signal -> Instance) (ty: Kind)
  (x: denote ty) (y: denote ty): state CavaState Datatypes.unit :=
match ty, x, y with
| Tuple l r, (x1,x2), (y1, y2) =>
  mapMSignals2 f l x1 y1 ;;
  mapMSignals2 f r x2 y2 ;;
  ret tt
| Unit, _, _ => ret tt
| Bit, x1, y1 =>
  addInstance (f x1 y1) ;;
  ret tt
| Vector n t, v1, v2 =>
  mapT (fun '(x, y)  => mapMSignals2 f t x y) (map2 pair v1 v2) ;;
  ret tt
end.

Section NetlistEval.
  Local Open Scope monad_scope.
  Local Open Scope string_scope.

  #[refine] Instance NetlistCategory : Category Kind := {
    morphism X Y := denote X -> state CavaState (denote Y);
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

  Program Instance NetlistArrow : Arrow Kind NetlistCategory Unit Tuple := {
    first X Y Z f '(z,y) :=
      x <- f z ;;
      ret (x,y);

    second X Y Z f '(y,z) :=
      x <- f z ;;
      ret (y,x);

    cancelr X '(x,_) := ret x;
    cancell X '(_,x) := ret x;

    uncancell _ x := ret (tt, x);
    uncancelr _ x := ret (x, tt);

    assoc _ _ _ '((x,y),z) := ret (x,(y,z));
    unassoc _ _ _ '(x,(y,z)) := ret ((x,y),z);
  }.

  Instance NetlistDrop : ArrowDrop NetlistArrow := { drop _ x := ret Datatypes.tt }.
  Instance NetlistCopy : ArrowCopy NetlistArrow := { copy _ x := ret (x,x) }.
  Instance NetlistSwap : ArrowSwap NetlistArrow := { swap _ _ '(x,y) := ret (y,x) }.

  Instance NetlistLoop : ArrowLoop NetlistArrow := {
    loopr _ _ Z f x :=
      z <- build Z ;;
      '(y,z') <- f (x,z) ;;
      mapMSignals2 (fun x y => AssignBit x y) Z z z' ;;
      ret y;

    loopl _ _ Z f x :=
      z <- build Z ;;
      '(z',y) <- f (z,x) ;;
      mapMSignals2 (fun x y => AssignBit x y) Z z z' ;;
      ret y;
  }.

  #[refine] Instance NetlistCava : Cava := {
    cava_arrow := NetlistArrow;

    constant b _ := match b with
      | true => ret Vcc
      | false => ret Gnd
      end;

    constant_bitvec n v _ := ret ( Vector.map
    (fun b => match b with
      | true => Vcc
      | false => Gnd
    end) (nat_to_bitvec_sized n (N.to_nat v)));

    not_gate i :=
      o <- newWire ;;
      addInstance (Not i o) ;;
      ret o;

    and_gate '(i0,i1) :=
      o <- newWire ;;
      addInstance (And i0 i1 o) ;;
      ret o;

    nand_gate '(i0,i1) :=
      o <- newWire ;;
      addInstance (Nand i0 i1 o) ;;
      ret o;

    or_gate '(i0,i1) :=
      o <- newWire ;;
      addInstance (Or i0 i1 o) ;;
      ret o;

    nor_gate '(i0,i1) :=
      o <- newWire ;;
      addInstance (Nor i0 i1 o) ;;
      ret o;

    xor_gate '(i0,i1) :=
      o <- newWire ;;
      addInstance (Xor i0 i1 o) ;;
      ret o;

    xnor_gate '(i0,i1) :=
      o <- newWire ;;
      addInstance (Xnor i0 i1 o) ;;
      ret o;

    buf_gate 'i :=
      o <- newWire ;;
      addInstance (Buf i o) ;;
      ret o;

    delay_gate X x :=
      y <- build X ;;
      mapMSignals2 (fun x y => DelayBit x y) X x y ;;
      ret y;

    xorcy '(i0, i1) :=
      o <- newWire ;;
      addInstance (Component "XORCY" [] [("O", o); ("CI", i0); ("LI", i1)]) ;;
      ret o;

    muxcy '(s,(ci, di)) :=
      o <- newWire ;;
      addInstance ( Component "MUXCY" [] [("O", o); ("S", s); ("CI", ci); ("DI", di)]) ;;
      ret o;

    unsigned_add m n s '(x, y) :=
      sum <- newWiresVec s ;;
      addInstance (UnsignedAdd (to_list x) (to_list y) (to_list sum)) ;;
      ret sum;

    lut n f is :=
      let seq := seq 0 (2^n) in
      let f' := NaryFunctions.nuncurry bool bool n f in
      let powers := map
        (fun p => let bv := Ndigits.N2Bv_sized n (N.of_nat p) in
                  2^(N.of_nat p) * N.b2n (f' (vec_to_nprod _ n bv))
        )%N
        seq in
      let config := fold_left N.add powers 0%N in
      let component_name := ("LUT" ++ string_of_uint (Nat.to_uint n))%string in
      let inputs := map
        (fun '(i, n) => ("I" ++ string_of_uint (Nat.to_uint i), n))%string
        (combine seq (to_list is)) in
      o <- newWire ;;
      let component :=
        Component
        component_name [("INIT", HexLiteral (2^n) config)]
        (("O", o) :: inputs) in
      addInstance component;;
      ret o;

  index_vec n o '(array, index) :=
      (* TODO: this can build the wire structure, but doesn't do the actual indexing yet *)
      build o;

  slice_vec n x y o H1 H2 vec :=
      (* TODO: this can build the wire structure, but doesn't do the actual indexing yet *)
      build (Vector (x - y + 1) o);

  to_vec o i := ret [i]%vector;
  append n o '(array, e) :=
    let result := (e :: array)%vector in
    ret result;
  concat n m o '(x, y) := ret (Vector.append x y);
  split n m o H x :=
    ret (@Vector.splitat (denote o) m (n - m) _);
  }.
  Proof.
    - assert ( m + (n - m) = n).
      omega.
      rewrite H0.
      apply x.
  Defined.

  Close Scope string_scope.

End NetlistEval.
