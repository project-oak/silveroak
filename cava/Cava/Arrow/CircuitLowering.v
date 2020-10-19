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
From Cava Require Import Arrow.Classes.Arrow.
From Cava Require Import Arrow.Classes.Category.
From Cava Require Import Arrow.Classes.Kleisli.
From Cava Require Import Arrow.Primitives.
From Cava Require Import Arrow.CircuitArrow VectorUtils BitArithmetic Types Signal Netlist.
From Cava Require Import Arrow.ArrowKind.

Import NilZero.

Import VectorNotations.
Import EqNotations.
Import ListNotations.
Import CategoryNotations.

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

(* number of bits when packing a CircuitLowering.Kind as a vector of bits *)
Fixpoint packed_width (ty: Kind): nat :=
match ty with
| Tuple l r => (packed_width l) + (packed_width r)
| Unit => 0
| Bit => 1
| Vector t n => n * packed_width t
end.

Fixpoint flatten_vector {T n m} (v: Vector.t (Vector.t T m) n): Vector.t T (n * m) :=
match v with
| [] => []
| x :: xs => x ++ flatten_vector xs
end.

Fixpoint const_wire (ty: Kind) (val: denote_kind ty): denote ty :=
match ty, val with
| Tuple l r, (lx,rx) => (const_wire l lx, const_wire r rx)
| Unit, _=> tt
| Bit, b => if b then Vcc else Gnd
| Vector t n, vec => Vector.map (const_wire t) vec
end.

Fixpoint unflatten_vector {T n m} (v: Vector.t (denote T) (n*m)):
  Vector.t (Vector.t (denote T) m) n :=
  match n with
  | 0 => []
  | S n' =>
    let (chunk, xs) := splitat (r:=n'*m) m (resize_default (const_wire _ (kind_default _)) _ v) in
    chunk :: unflatten_vector xs
  end.

(* pack any CircuitLowering.Kind as a Vector.t of Netlist.Kind bits *)
Fixpoint pack (ty: Kind) (s: denote ty) {struct ty}: Vector.t (Signal Kind.Bit) (packed_width ty) :=
  match ty as k return (denote k -> t (Signal Kind.Bit) (packed_width k)) with
  | Tuple ty1 ty2 => fun '(x,y) => pack ty1 x ++ pack ty2 y
  | Unit => fun _ => []
  | Bit => fun b => [b]
  | Vector ty0 n => fun x => flatten_vector (Vector.map (pack ty0) x)
  end s.

Fixpoint unpack (ty: Kind) (v: Vector.t (Signal Kind.Bit) (packed_width ty)): denote ty :=
  match ty as k return (t (Signal Kind.Bit) (packed_width k) -> denote k) with
  | Tuple ty1 ty2 => fun v =>
    let (l, r) := splitat (packed_width ty1) v in
    (unpack ty1 l, unpack ty2 r)
  | Unit => fun _ => tt
  | Bit => fun v => v[@Fin.F1]
  | Vector ty n => fun v =>
    Vector.map (unpack ty) (unflatten_vector (T:=Bit) (n:=n) (m:=packed_width ty) v)
  end v.

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

Fixpoint map2M (f: Signal Kind.Bit -> Signal Kind.Bit -> Instance) (ty: Kind)
  (x: denote ty) (y: denote ty): state CavaState Datatypes.unit :=
  match ty, x, y with
  | Tuple l r, (x1,x2), (y1, y2) =>
    map2M f l x1 y1 ;;
    map2M f r x2 y2 ;;
    ret tt
  | Unit, _, _ => ret tt
  | Bit, x1, y1 =>
    addInstance (f x1 y1) ;;
    ret tt
  | Vector t n, v1, v2 =>
    mapT (fun '(x, y)  => map2M f t x y) (map2 pair v1 v2) ;;
    ret tt
  end.

Definition slice' n x y (o: Kind) (v: denote (Vector o n)) : state CavaState (denote (Vector o (x - y + 1))) :=
  let length := x - y + 1 in
  let packed := VecLit (pack _ v) in
  wires <- newVector Kind.Bit (packed_width (Vector o n))  ;;
  addInstance (AssignSignal wires packed) ;;
  let sliced := Slice y (length * packed_width o) wires in

  sliced_wires <- newVector Kind.Bit (length * packed_width o)  ;;
  addInstance (AssignSignal sliced_wires sliced) ;;

  let packed := Vector.map (IndexConst sliced_wires) (vseq 0 (length * packed_width o)) in
  let unpacked := unpack (Vector o length) packed in

  ret unpacked.

Definition index' n (o: Kind): denote (Vector o n) -> denote (vec_index n) -> state CavaState (denote o) :=
  (* Avoid zero width indexing *)
  match n return denote (Vector o n) -> denote (vec_index n) -> state CavaState (denote o) with
  | 0 => fun _ _ => ret (const_wire o (kind_default _))
  | S 0 => fun array _ => ret (Vector.hd (n:=0) array)
  | S (S _) => fun array index =>
      let array := Vector.map VecLit (pack_vector _ _ array) in
      let indexed := IndexAt (VecLit array) (VecLit index) in
      wires <- newVector Kind.Bit (packed_width o) ;;
      addInstance (AssignSignal wires indexed) ;;
      let packed := Vector.map (IndexConst wires) (vseq 0 (packed_width o)) in
      ret (unpack o packed)
  end.

(* Local Notation "'kleisli'" := (kleisli_arrow (state CavaState) _)(at level 100). *)

Definition netlist_category : Category Kind
  := build_denoted_kleisli_category Kind denote (state CavaState) _.

Definition netlist_arrow : Arrow Kind netlist_category Unit Tuple
  := build_denoted_kleisli_arrow Kind denote (state CavaState) _ Unit Tuple tt
    (fun _ _ => pair)
    (fun _ _ => fst)
    (fun _ _ => snd).

Instance netlist_drop : Arrows.Drop netlist_arrow := { drop _ _ := ret tt; }.
Instance netlist_copy : Arrows.Copy netlist_arrow := { copy _ x := ret (x,x); }.
Instance netlist_swap : Arrows.Swap netlist_arrow := { swap _ _ '(x,y) := ret (y,x); }.
Instance netlist_arrow_rewrite_or_default : Arrows.RewriteOrDefault netlist_arrow := {
  rewrite_or_default x y a :=
    match eq_kind_dec x y with
    | left Heq => ret (rew Heq in a)
    | right _ => ret (const_wire _ (kind_default _))
    end;
}.

Instance netlist_annotation : Arrows.Annotation netlist_arrow String.string := {
  annotate _ _ _ f := f
}.

Instance netlist_impossible : Arrows.Impossible netlist_arrow := {
  impossible _ _ _ := ret (const_wire _ (kind_default _))
}.

Instance netlist_loop : Arrows.Loop netlist_arrow := {
  loopr _ _ Z f x :=
      z <- fresh_wire Z ;;
      '(y,z') <- f (x,z) ;;
      map2M (fun x y => AssignSignal x y) Z z z' ;;
      ret y;

  loopl _ _ Z f x :=
      z <- fresh_wire Z ;;
      '(z',y) <- f (z,x) ;;
      map2M (fun x y => AssignSignal x y) Z z z' ;;
      ret y;
}.

Instance netlist_primitive : Arrows.Primitive netlist_arrow CircuitPrimitive primitive_input primitive_output := {
  primitive p :=
  match p with
  | (Constant ty val) => fun _ => ret (const_wire ty val)
  | (ConstantVec n ty val) => fun _ =>
    ret (const_wire (Vector ty n) (resize_default (kind_default _) n (Vector.of_list val)))
  | (Delay o) => fun x =>
      y <- fresh_wire _ ;;
      map2M (fun x y => DelayBit x y) _ (fst x) y ;;
      ret y
  | Primitives.Not => fun i =>
      o <- newWire ;;
      addInstance (Not (fst i) o) ;;
      ret o
  | BufGate => fun i =>
      o <- newWire ;;
      addInstance (Buf (fst i) o) ;;
      ret o
  | (Uncons n o) => fun v => ret ((Vector.hd (fst v), Vector.tl (fst v)))
  | (Unsnoc n o) => fun v => ret (unsnoc (fst v))
  | (Primitives.Slice n x y o) => fun v => slice' n x y o (fst v)
  | (Primitives.Split n m o) => fun x => ret (Vector.splitat n (fst x))
  | (EmptyVec o) => fun _ => ret ([])
  | (Lut n f) => fun '(is,_) =>
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

  | (Primitives.Fst X Y) => fun '((x,y),_) => ret x
  | (Primitives.Snd _ _) => fun '((x,y),_) => ret y
  | (Primitives.Pair _ _) => fun '(x,(y,_)) => ret (x,y)

  | Primitives.And => fun '(x,(y,_)) =>
      o <- newWire ;;
      addInstance (And x y o) ;;
      ret o
  | Primitives.Nand => fun '(x,(y,_)) =>
      o <- newWire ;;
      addInstance (Nand x y o) ;;
      ret o
  | Primitives.Or => fun '(x,(y,_)) =>
      o <- newWire ;;
      addInstance (Or x y o) ;;
      ret o
  | Primitives.Nor => fun '(x,(y,_)) =>
      o <- newWire ;;
      addInstance (Nor x y o) ;;
      ret o
  | Primitives.Xor => fun '(i0,(i1,_)) =>
      o <- newWire ;;
      addInstance (Xor i0 i1 o) ;;
      ret o
  | Primitives.Xnor => fun '(i0,(i1,_)) =>
      o <- newWire ;;
      addInstance (Xnor i0 i1 o) ;;
      ret o
  | Primitives.Xorcy => fun '(i0, (i1, _)) =>
      o <- newWire ;;
      addInstance (Component "XORCY" [] [("O", USignal o); ("CI", USignal i0); ("LI", USignal i1)]) ;;
      ret o
  | Muxcy => fun '(s,((ci, di), _)) =>
      o <- newWire ;;
      addInstance ( Component "MUXCY" [] [("O", USignal o); ("S", USignal s); ("CI", USignal ci); ("DI", USignal di)]) ;;
      ret o
  | (Primitives.UnsignedAdd m n s) => fun '(x,(y,_)) =>
      sum <- newVector _ s ;;
      addInstance (UnsignedAdd (VecLit x) (VecLit y) sum) ;;
      ret (Vector.map (IndexConst sum) (vseq 0 s))
  | (Primitives.UnsignedSub s) => fun '(x, (y,_)) =>
      sum <- newVector _ s ;;
      addInstance (UnsignedSubtract (VecLit x) (VecLit y) sum) ;;
      ret (Vector.map (IndexConst sum) (vseq 0 s))
  | (Index n o) => fun '(v,(i,_)) => index' _ _ v i
  | (Primitives.Cons n o) => fun '(x, (v,_)) =>
    ret ((x :: v)%vector)
  | (Snoc n o) => fun '(v, (x,_)) => ret (snoc v x)
  | (Primitives.Concat n m o) => fun '(x, (y, _)) =>
    ret ((x ++ y)%vector)
  end;
}.

Fixpoint apply_rightmost_tt (x: Kind)
  : denote (remove_rightmost_unit x) -> denote x
  :=
  match x as x' return denote (remove_rightmost_unit x') -> denote x' with
  | Tuple l r =>
    let rec := apply_rightmost_tt r in
    match r as r' return
      (denote (remove_rightmost_unit r') -> denote r') ->
        denote (remove_rightmost_unit (Tuple l r')) -> denote (Tuple l r')
      with
    | Unit => fun f x => (x, tt)
    | _ => fun f p => (fst p, f (snd p))
    end rec
  | _ => fun x => x
  end.

From Cava Require Import Arrow.ExprLowering.
Definition build_netlist {X Y} (circuit: ExprSyntax.Kappa X Y)
  (i: denote (remove_rightmost_unit X))
  : state CavaState (denote Y) :=
  (closure_conversion (arrow:=netlist_arrow) circuit) (apply_rightmost_tt X i).

