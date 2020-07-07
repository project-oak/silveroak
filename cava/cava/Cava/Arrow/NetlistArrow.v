(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

From Coq Require Import Bool ZArith NaryFunctions Vector String List DecimalString Lia.
From Arrow Require Import Category Arrow Kleisli.
From Cava Require Import Arrow.CavaArrow VectorUtils BitArithmetic Types Signal Netlist.

Import NilZero.

Import VectorNotations.
Import EqNotations.
Import ListNotations.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Export Data.Monads.StateMonad.

Import MonadNotation.

(******************************************************************************)
(* Evaluation as a netlist                                                    *)
(******************************************************************************)

Fixpoint denote (ty: Kind): Type :=
match ty with
| Tuple l r => prod (denote l) (denote r)
| Unit => Datatypes.unit
| Bit => Signal Kind.Bit
| Vector t n => Vector.t (denote t) n
end.

(* number of bits when packing a NetlistArrow.Kind as a vector of bits *)
Fixpoint packed_width (ty: Kind): nat :=
match ty with
| Tuple l r => (packed_width l) + (packed_width r)
| Unit => 0
| Bit => 1
| Vector t n => n * packed_width t
end.

Lemma pack_tuple_size: forall l r, packed_width l + packed_width r = packed_width <<l, r>>.
Proof. auto. Qed.

Fixpoint flatten_vector {T n m} (v: Vector.t (Vector.t T m) n): Vector.t T (n * m) :=
match v with
| [] => []
| x :: xs => x ++ flatten_vector xs
end.

Definition unflatten_vector {T n m} (v: Vector.t T (n*m)): Vector.t (Vector.t T m) n.
Proof.
  induction n.
  exact [].
  rewrite Nat.mul_succ_l in v.
  rewrite Nat.add_comm in v.
  apply (splitat m) in v.
  inversion v.
  apply IHn in X0.
  exact (X :: X0).
Defined.

(* pack any NetlistArrow.Kind as a Vector.t of netlist bits *)
Fixpoint pack (ty: Kind) (s: denote ty) {struct ty}: Vector.t (Signal Kind.Bit) (packed_width ty).
Proof.
  destruct ty; simpl in *.
  - inversion s as [s1 s2].
    exact (pack ty1 s1 ++ pack ty2 s2).
  - exact [].
  - exact [s].
  - pose (Vector.map (pack ty) s) as x.
    exact (flatten_vector x).
Defined.

Fixpoint unpack (ty: Kind) (v: Vector.t (Signal Kind.Bit) (packed_width ty)): denote ty.
Proof.
  destruct ty; simpl in *.
  - apply (splitat (packed_width ty1)) in v.
    inversion v as [v1 v2].
    exact (unpack ty1 v1, unpack ty2 v2).
  - exact tt.
  - exact (Vector.nth v Fin.F1).
  - apply (unflatten_vector) in v.
    exact (Vector.map (unpack ty) v).
Defined.

Definition pack_vector n ty (vec: denote (Vector ty n))
  : Vector.t (Vector.t (Signal Kind.Bit) (packed_width ty)) n
  := Vector.map (pack _) vec.

Fixpoint build (ty: Kind) : state CavaState (denote ty) :=
match ty with
| Tuple l r =>
  l <- build l;;
  r <- build r;;
  ret (l, r)
| Unit => ret tt
| Bit => newWire
| Vector t n => mapT (fun _ => build t) (const tt n)
end.

Fixpoint mapMSignals2 (f: Signal Kind.Bit -> Signal Kind.Bit -> Instance) (ty: Kind)
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
| Vector t n, v1, v2 =>
  mapT (fun '(x, y)  => mapMSignals2 f t x y) (map2 pair v1 v2) ;;
  ret tt
end.

Section NetlistEval.
  Local Open Scope monad_scope.
  Local Open Scope string_scope.

  Instance NetlistCategory : Category Kind := {
    morphism X Y := denote X -> state CavaState (denote Y);
    id X x := ret x;
    compose X Y Z f g := g >=> f;
  }.

  Local Notation "'kleisli'" := (kleisli_arrow (state CavaState) _)(at level 100).

  Program Instance NetlistArrow : Arrow Kind NetlistCategory Unit Tuple := {
    first X Y Z := first (Arrow:=kleisli);
    second X Y Z := second (Arrow:=kleisli); 
    assoc   X Y Z := assoc (Arrow:=kleisli); 
    unassoc X Y Z := unassoc (Arrow:=kleisli);  
    cancelr X := cancelr (Arrow:=kleisli);  
    cancell X := cancell (Arrow:=kleisli);  
    uncancell X := uncancell (Arrow:=kleisli);  
    uncancelr x := uncancelr (Arrow:=kleisli);  
  }.

  Instance NetlistDrop : ArrowDrop NetlistArrow := { drop _ x := ret Datatypes.tt }.
  Instance NetlistCopy : ArrowCopy NetlistArrow := { copy _ x := ret (x,x) }.
  Instance NetlistSwap : ArrowSwap NetlistArrow := { swap _ _ '(x,y) := ret (y,x) }.
  Instance NetlistSTKC : ArrowSTKC NetlistArrow := {}.

  Instance NetlistLoop : ArrowLoop NetlistArrow := {
    loopr _ _ Z f x :=
      z <- build Z ;;
      '(y,z') <- f (x,z) ;;
      mapMSignals2 (fun x y => AssignSignal x y) Z z z' ;;
      ret y;

    loopl _ _ Z f x :=
      z <- build Z ;;
      '(z',y) <- f (z,x) ;;
      mapMSignals2 (fun x y => AssignSignal x y) Z z z' ;;
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
      sum <- newVector _ s ;;
      addInstance (UnsignedAdd (VecLit x) (VecLit y) sum) ;;
      ret (Vector.map (IndexConst sum) (vseq 0 s));

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

  empty_vec o _ := ret []%vector;
  index n o '(array, index) := _;

  cons n o '(x, v) := _;
  snoc n o '(v, x) := _;
  uncons n o v := _; 
  unsnoc n o v := _; 
  concat n m o '(x, y) := ret (Vector.append x y);

  split n m o H x :=
    ret (@Vector.splitat (denote o) m (n - m) _);

  slice n x y o H1 H2 v := _;
  }.
  Proof.
    (* TODO: clean up *)
    (*index*)
    - apply pack_vector in array.
      apply (Vector.map VecLit) in array.
      pose (IndexAt (VecLit array) (VecLit index)). 
      pose (Vector.map (IndexConst s) (vseq 0 (packed_width o))).
      apply (unpack o) in t.
      exact (ret t).
    (*cons*)
    - exact (ret ((x :: v)%vector) ).
    (*snoc*)
    - refine (let v := ((v ++ [x])%vector) in ret _).
      destruct (Nat.eq_dec (n+1) (S n)).
      rewrite e in v.
      exact v.
      exfalso;lia. 
    (*uncons*)
    - exact (ret ((Vector.hd v, Vector.tl v)) ).
    (*unsnoc*)
    - refine (ret ((Vector.take n _ v, Vector.last v)) ).
      auto.
    (*split*)
    - destruct (Nat.eq_dec (m + (n-m)) n).
      rewrite <- e in x.
      exact x.
      exfalso;lia.
    (*slice*)
    - apply pack_vector in v.
      apply (Vector.map VecLit) in v.
      refine(
        let length := (x - y + 1) in 
        let sliced := (Slice x length (VecLit v)) in
        let smashed := Vector.map (IndexConst sliced) (vseq 0 length) in
        let smashier := Vector.map (fun elem => Vector.map (IndexConst elem) (vseq 0 (packed_width o))) smashed in
        let unpacked := Vector.map (unpack o) smashier in
        ret unpacked
      ).
  Defined.

  Close Scope string_scope.
  Local Open Scope category_scope.

  Definition arrow_netlist {X Y} (circuit: X ~[NetlistCava]~> Y)
    : denote X -> state CavaState (denote Y) :=
    circuit.

End NetlistEval.