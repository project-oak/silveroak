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


(******************************************************************************)
(* The following lemmas and definitions connect the types representable by
  Arrow.Kind and the netlist Kind.Kind, and the Signal _ representations used
  by the underlying netlist.
*)

Fixpoint netlist_compatible_in_vec (ty: Kind): bool :=
match ty with
| Bit => true
| Vector ty' _ => netlist_compatible_in_vec ty'
| _ => false
end.

Fixpoint netlist_compatible (ty: Kind): bool :=
match ty with
| Bit => true
| Tuple l r => netlist_compatible l && netlist_compatible r
| Unit => true
| Vector ty' _ => netlist_compatible_in_vec ty'
end.

Fixpoint only_bits (ty: Kind) := 
match ty with
| Bit => True
| Tuple l r => False
| Unit => False
| Vector ty' _ => only_bits ty'
end.

Hint Unfold only_bits : core.

Lemma only_bits_contra: forall l r, only_bits (Tuple l r) -> False.
Proof. auto. Qed.

Fixpoint denote_as_kind_kind (ty: Kind): only_bits ty -> Kind.Kind :=
match ty with
| Tuple _ _ => fun H => match only_bits_contra _ _ H with end
| Unit => fun H => Kind.Void
| Bit => fun H => Kind.Bit
| Vector t n => fun H => Kind.BitVec (denote_as_kind_kind t H) n
end.

Fixpoint only_bits_in_vec (ty: Kind) := 
match ty with
| Bit => True
| Tuple l r => only_bits_in_vec l /\ only_bits_in_vec r
| Unit => True
| Vector ty' _ => only_bits ty'
end.

Hint Unfold only_bits_in_vec : core.

Lemma only_bits_in_vec_inr: forall l r, only_bits_in_vec (Tuple l r) -> only_bits_in_vec r.
Proof. intros. inversion H. auto. Qed.

Lemma only_bits_in_vec_inl: forall l r, only_bits_in_vec (Tuple l r) -> only_bits_in_vec l.
Proof. intros. inversion H. auto. Qed.

Lemma only_bits_in_vec': forall x, only_bits x -> only_bits_in_vec x.
Proof. 
  intros. 
  destruct x; auto.
  contradiction.
Defined.

Fixpoint denote_as_netlist_signal (ty: Kind): only_bits_in_vec ty -> Type :=
match ty with
| Tuple l r => fun H =>
  prod
    (denote_as_netlist_signal l (only_bits_in_vec_inl _ _ H))
    (denote_as_netlist_signal r (only_bits_in_vec_inr _ _ H))
| Unit => fun H => Datatypes.unit
| Bit => fun H => Signal Kind.Bit
| Vector t n => fun H => Signal (Kind.BitVec (denote_as_kind_kind t H) n)
end.

Definition rewrite_denotation: forall ty H,
  denote_as_netlist_signal ty (only_bits_in_vec' _ H) ->
  Signal (denote_as_kind_kind ty H).
Proof.
  intros.
  induction ty; simpl in *; auto.
  - contradiction.
  - contradiction.
Defined.

Fixpoint denote_convert (ty: Kind) (H: only_bits_in_vec ty) {struct ty}: denote ty -> denote_as_netlist_signal ty H.
Proof.
  intros; destruct ty.
  - inversion X.
    apply (denote_convert ty1 (only_bits_in_vec_inl _ _ H)) in X0.
    apply (denote_convert ty2 (only_bits_in_vec_inr _ _ H)) in X1.
    simpl in *.
    exact ((X0, X1)).
  - exact tt. 
  - simpl in *; exact X.
  - simpl in *.
    apply (Vector.map (denote_convert ty (only_bits_in_vec' _ H))) in X.
    apply (Vector.map (rewrite_denotation _ _) ) in X.
    exact (VecLit X).
Defined.

Definition unrewrite_denotation: forall ty H,
  Signal (denote_as_kind_kind ty H) -> 
  denote_as_netlist_signal ty (only_bits_in_vec' _ H).
Proof.
  intros.
  induction ty; simpl in *; auto.
  - contradiction.
  - contradiction.
Defined.

Fixpoint denote_unconvert (ty: Kind) (H: only_bits_in_vec ty) {struct ty}: 
  denote_as_netlist_signal ty H -> denote ty.
Proof.
  intros; destruct ty.
  - inversion X.
    apply (denote_unconvert ty1 (only_bits_in_vec_inl _ _ H)) in X0.
    apply (denote_unconvert ty2 (only_bits_in_vec_inr _ _ H)) in X1.
    simpl in *.
    exact ((X0, X1)).
  - exact tt. 
  - simpl in *; exact X.
  - simpl in *.
    pose (Vector.map (IndexConst X) (vseq 0 n)).
    apply (Vector.map (unrewrite_denotation _ _) ) in t.
    exact (Vector.map (denote_unconvert ty (only_bits_in_vec' _ H)) t).
Defined.

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

  cons n o '(x, v) := _; (* Some (x :: v); *)
  snoc n o '(v, x) := _; (* let v' := Some (v ++ [x])%vector in _; *)
  uncons n o v := _; (* Some (hd v, tl v); *)
  unsnoc n o v := _; (* Some (take n _ v, last v); *)
  concat n m o '(x, y) := ret (Vector.append x y);

  split n m o H x :=
    ret (@Vector.splitat (denote o) m (n - m) _);

  slice n x y o H1 H2 v := _;
  }.
  Proof.
    (* TODO: fix for non Vector Bit 
      currently vector operations on Vector T where T != Bit return dummy wiring.
    *)
    (*index*)
    - destruct o.
      exact (build _).
      exact (build _).
      exact (ret (IndexAt (VecLit array) (VecLit index))). 
      exact (build _).
    (*cons*)
    - exact (ret ((x :: v)%vector) ).
    (*snoc*)
    - refine (let v := ((v ++ [x])%vector) in ret _).
      assert (n + 1 = S n). lia.
      rewrite H in v.
      exact v.
    (*uncons*)
    - exact (ret ((Vector.hd v, Vector.tl v)) ).
    (*unsnoc*)
    - refine (ret ((Vector.take n _ v, Vector.last v)) ).
      auto.
    (*split*)
    - assert ( m + (n - m) = n).
      lia.
      rewrite H0.
      apply x.
    (*slice*)
    - 
      destruct o.
      exact (build _).
      exact (build _).
      refine (
        let length := (x - y + 1) in 
        let sliced := (Slice x length (VecLit v)) in
        let smashed := (Vector.map (IndexConst sliced) (vseq 0 length)) in
        ret smashed).
      exact (build _).
  Defined.

  Close Scope string_scope.
  Local Open Scope category_scope.

  Definition netlist_friendly {X Y}
    (circuit: denote X -> state CavaState (denote Y))
    (H1: only_bits_in_vec X)
    (H2: only_bits_in_vec Y)
    : denote_as_netlist_signal X H1 -> state CavaState (denote_as_netlist_signal Y H2).
  Proof.
    intros.
    apply (denote_unconvert) in X0.
    apply circuit in X0.
    exact (
      v <- X0;;
      ret (denote_convert Y H2 v)
    ).
  Defined.

  Definition wf_netlist_io {X Y} (circuit: X ~> Y) :=
    only_bits_in_vec X /\
    only_bits_in_vec Y.

  Lemma wf_netlist_io_left: 
    forall {X Y} {circuit: X ~> Y},
    wf_netlist_io circuit -> only_bits_in_vec X.
  Proof. intros. inversion H. auto. Qed.

  Lemma wf_netlist_io_right: 
    forall {X Y} {circuit: X ~> Y},
    wf_netlist_io circuit -> only_bits_in_vec Y.
  Proof. intros. inversion H. auto. Qed.

  Definition arrow_netlist {X Y} (circuit: X ~[NetlistCava]~> Y)
    (H: wf_netlist_io circuit): 
    denote_as_netlist_signal X (wf_netlist_io_left H) -> state CavaState (denote_as_netlist_signal Y (wf_netlist_io_right H)) :=
    netlist_friendly circuit _ _.

End NetlistEval.