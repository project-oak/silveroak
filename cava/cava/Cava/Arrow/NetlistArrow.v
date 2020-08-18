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

(* pack any NetlistArrow.Kind as a Vector.t of Netlist.Kind bits *)
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

Fixpoint fresh_wire (ty: Kind) : state CavaState (denote ty) :=
match ty with
| Tuple l r =>
  l <- fresh_wire l;;
  r <- fresh_wire r;;
  ret (l, r)
| Unit => ret tt
| Bit => newWire
| Vector t n => mapT (fun _ => fresh_wire t) (const tt n)
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

Definition snoc' n o (v: denote (Vector o n)) a
  : denote (Vector o (S n)) :=
  t_rect _ (fun n v => denote (Vector o (S n))) [a]
  (fun x n v f => 
    x :: f
  ) _ v.

Definition slice' n x y (o: Kind) (v: denote (Vector o n)) : state CavaState (denote (Vector o (x - y + 1))) := 
  let v := Vector.map VecLit (pack_vector _ _ v) in
  let length := x - y + 1 in
  let sliced := (Slice x length (VecLit v)) in
  let smashed := Vector.map (IndexConst sliced) (vseq 0 length) in
  let smashier := Vector.map (fun elem => Vector.map (IndexConst elem) (vseq 0 (packed_width o))) smashed in
  let unpacked := Vector.map (unpack o) smashier in
  ret unpacked.

Definition index' n (o: Kind) (array: denote (Vector o n)) (index: denote (vec_index n))
  : state CavaState (denote o) := 
  let array := Vector.map VecLit (pack_vector _ _ array) in 
  let index := (IndexAt (VecLit array) (VecLit index)) in
  let packed := Vector.map (IndexConst index) (vseq 0 (packed_width o)) in
  ret (unpack o packed).

Local Notation "'kleisli'" := (kleisli_arrow (state CavaState) _)(at level 100).

Fixpoint build_netlist' {i o}
  (c: Circuit i o)
  : denote i ->
    state CavaState (denote o) :=
  match c with
  | Composition _ _ _ f g => build_netlist' f >=> build_netlist' g
  | First x y z f => first (Arrow:=kleisli) (build_netlist' f)
  | Second x y z f => second (Arrow:=kleisli) (build_netlist' f)

  | Structural (Id _) => ret
  | Structural (Cancelr X) => cancelr (Arrow:=kleisli)  
  | Structural (Cancell X) => cancell (Arrow:=kleisli)
  | Structural (Uncancell _) => uncancell (Arrow:=kleisli)
  | Structural (Uncancelr _) => uncancelr (Arrow:=kleisli)
  | Structural (Assoc _ _ _) => assoc (Arrow:=kleisli)
  | Structural (Unassoc _ _ _) => unassoc (Arrow:=kleisli)
  | Structural (Drop x) => fun _ => ret tt
  | Structural (Swap x y) => fun '(x,y) => ret (y,x)
  | Structural (Copy x) => fun x => ret (x,x)

  | Loopr _ _ Z f => fun x => 
      z <- fresh_wire Z ;;
      '(y,z') <- (build_netlist' f) (x,z) ;;
      mapMSignals2 (fun x y => AssignSignal x y) Z z z' ;;
      ret y
  
  | Loopl _ _ Z f => fun x => 
      z <- fresh_wire Z ;;
      '(z',y) <- (build_netlist' f) (z,x) ;;
      mapMSignals2 (fun x y => AssignSignal x y) Z z z' ;;
      ret y

  | Primitive (constant b) => fun _ =>
    match b with
    | true => ret Vcc
    | false => ret Gnd
    end
  | Primitive (constant_bitvec n v) => fun _ =>
    ret (Vector.map
    (fun b => match b with
      | true => Vcc
      | false => Gnd
    end) (nat_to_bitvec_sized n (N.to_nat v)))
  | Primitive (delay_gate o) => fun x =>
      y <- fresh_wire _ ;;
      mapMSignals2 (fun x y => DelayBit x y) _ (fst x) y ;;
      ret y
  | Primitive not_gate => fun i => 
      o <- newWire ;;
      addInstance (Not (fst i) o) ;;
      ret o
  | Primitive buf_gate => fun i => 
      o <- newWire ;;
      addInstance (Buf (fst i) o) ;;
      ret o
  | Primitive (uncons n o) => fun v => ret ((Vector.hd (fst v), Vector.tl (fst v)))
  | Primitive (unsnoc n o) => fun v => ret ((Vector.take n (Nat.le_succ_diag_r _) (fst v), Vector.last (fst v)))
  | Primitive (slice n x y o) => fun v => slice' n x y o (fst v)
  | Primitive (CavaArrow.split n m o) => fun x => ret (Vector.splitat n (fst x))
  | Primitive (empty_vec o) => fun _ => ret ([])
  | Primitive (lut n f) => fun '(is,_) =>
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
        (fun '(i, n) => ("I" ++ string_of_uint (Nat.to_uint i), USignal n))%string
        (combine seq (to_list is)) in
      o <- newWire ;;
      let component :=
        Component
        component_name [("INIT", HexLiteral (2^n) config)]
        (("O", USignal o) :: inputs) in
      addInstance component;;
      ret o

  | Primitive and_gate => fun '(x,(y,_)) => 
      o <- newWire ;;
      addInstance (And x y o) ;;
      ret o
  | Primitive nand_gate => fun '(x,(y,_)) => 
      o <- newWire ;;
      addInstance (Nand x y o) ;;
      ret o
  | Primitive or_gate => fun '(x,(y,_)) =>
      o <- newWire ;;
      addInstance (Or x y o) ;;
      ret o
  | Primitive nor_gate => fun '(x,(y,_)) =>
      o <- newWire ;;
      addInstance (Nor x y o) ;;
      ret o
  | Primitive xor_gate => fun '(i0,(i1,_)) =>
      o <- newWire ;;
      addInstance (Xor i0 i1 o) ;;
      ret o
  | Primitive xnor_gate => fun '(i0,(i1,_)) =>
      o <- newWire ;;
      addInstance (Xnor i0 i1 o) ;;
      ret o
  | Primitive xorcy => fun '(i0, (i1, _)) =>
      o <- newWire ;;
      addInstance (Component "XORCY" [] [("O", USignal o); ("CI", USignal i0); ("LI", USignal i1)]) ;;
      ret o
  | Primitive muxcy => fun '(s,((ci, di), _)) =>
      o <- newWire ;;
      addInstance ( Component "MUXCY" [] [("O", USignal o); ("S", USignal s); ("CI", USignal ci); ("DI", USignal di)]) ;;
      ret o
  | Primitive (unsigned_add m n s) => fun '(x,(y,_)) =>
      sum <- newVector _ s ;;
      addInstance (UnsignedAdd (VecLit x) (VecLit y) sum) ;;
      ret (Vector.map (IndexConst sum) (vseq 0 s))
  | Primitive (unsigned_sub s) => fun '(x, (y,_)) =>
      sum <- newVector _ s ;;
      (* TODO: add netlist subtraction instance *)
      addInstance (UnsignedAdd (VecLit x) (VecLit y) sum) ;;
      ret (Vector.map (IndexConst sum) (vseq 0 s))
  | Primitive (index n o) => fun '(v,(i,_)) => index' _ _ v i
  | Primitive (CavaArrow.cons n o) => fun '(x, (v,_)) =>
    ret ((x :: v)%vector)
  | Primitive (snoc n o) => fun '(v, (x,_)) => ret (snoc' _ _ v x)
  | Primitive (CavaArrow.concat n m o) => fun '(x, (y, _)) =>
    ret ((x ++ y)%vector)
end.

Close Scope string_scope.
Local Open Scope category_scope.

Definition build_netlist {X Y} (circuit: X ~> Y)
  : denote (remove_rightmost_unit X) -> state CavaState (denote Y) :=
  build_netlist' (insert_rightmost_tt1 _ >>> circuit).