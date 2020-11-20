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

From Coq Require Import Bool.Bool ZArith.ZArith Numbers.NaryFunctions
     Vectors.Vector Strings.String Lists.List Numbers.DecimalString
     micromega.Lia.
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
| Bit => Signal Signal.Bit
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
Fixpoint pack (ty: Kind) (s: denote ty) {struct ty}: Vector.t (Signal Signal.Bit) (packed_width ty) :=
  match ty as k return (denote k -> t (Signal Signal.Bit) (packed_width k)) with
  | Tuple ty1 ty2 => fun '(x,y) => pack ty1 x ++ pack ty2 y
  | Unit => fun _ => []
  | Bit => fun b => [b]
  | Vector ty0 n => fun x => flatten_vector (Vector.map (pack ty0) x)
  end s.

Fixpoint unpack (ty: Kind) (v: Vector.t (Signal Signal.Bit) (packed_width ty)): denote ty :=
  match ty as k return (t (Signal Signal.Bit) (packed_width k) -> denote k) with
  | Tuple ty1 ty2 => fun v =>
    let (l, r) := splitat (packed_width ty1) v in
    (unpack ty1 l, unpack ty2 r)
  | Unit => fun _ => tt
  | Bit => fun v => v[@Fin.F1]
  | Vector ty n => fun v =>
    Vector.map (unpack ty) (unflatten_vector (T:=Bit) (n:=n) (m:=packed_width ty) v)
  end v.

Definition pack_vector n ty (vec: denote (Vector ty n))
  : Vector.t (Vector.t (Signal Signal.Bit) (packed_width ty)) n
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

Fixpoint map2M (f: Signal Signal.Bit -> Signal Signal.Bit -> Instance) (ty: Kind)
  (x: denote ty) (y: denote ty): state CavaState Datatypes.unit :=
  match ty, x, y with
  | Tuple l r, (x1,x2), (y1, y2) =>
    map2M f l x1 y1 ;;
    map2M f r x2 y2
  | Unit, _, _ => ret tt
  | Bit, x1, y1 =>
    addInstance (f x1 y1)
  | Vector t n, v1, v2 =>
    mapT (fun '(x, y)  => map2M f t x y) (map2 pair v1 v2) ;;
    ret tt
  end.

Fixpoint rewrite_or_default (x y: Kind): denote x -> denote y :=
  match x as x' return denote x' -> denote y with
  | Unit =>
      match y with
      | Unit => fun a => a
      | _ => fun _ => (const_wire _ (kind_default _))
      end
  | Tuple l r =>
      match y with
      | Tuple ll rr => fun '(a,b) => (rewrite_or_default l ll a, rewrite_or_default r rr b)
      | _ => fun _ => (const_wire _ (kind_default _))
      end
  | Vector t n =>
      match y with
      | Vector t2 n2 => fun a => VectorUtils.resize_default (const_wire _ (kind_default _)) _ (Vector.map (rewrite_or_default t t2) a)
      | _ => fun _ => (const_wire _ (kind_default _))
      end
  | Bit =>
      match y with
      | Bit => fun a => a
      | _ => fun _ => (const_wire _ (kind_default _))
      end
  end.


Definition slice' n x y (o: Kind) (v: denote (Vector o n)) : state CavaState (denote (Vector o (x - y + 1))) :=
  let length := x - y + 1 in
  let packed := VecLit (pack _ v) in
  wires <- newVector Signal.Bit (packed_width (Vector o n))  ;;
  addInstance (AssignSignal wires packed) ;;
  let sliced := Slice y (length * packed_width o) wires in

  sliced_wires <- newVector Signal.Bit (length * packed_width o)  ;;
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
      wires <- newVector Signal.Bit (packed_width o) ;;
      addInstance (AssignSignal wires indexed) ;;
      let packed := Vector.map (IndexConst wires) (vseq 0 (packed_width o)) in
      ret (unpack o packed)
  end.

Local Notation "'kleisli'" := (kleisli_arrow (state CavaState) _)(at level 100).

Definition nullary_primitive_netlist x (p: NullaryPrimitive x)
  : state CavaState (denote x) :=
  match p with
  | Constant ty val => ret (const_wire ty val)
  | ConstantVec n ty val =>
    ret (const_wire (Vector ty n) (resize_default (kind_default _) n (Vector.of_list val)))
  | EmptyVec o => ret ([])
  end.

Definition unary_primitive_netlist x y (p: UnaryPrimitive x y)
  : denote x -> state CavaState (denote y) :=
  match p with
  | Primitives.Not => fun i =>
      o <- newWire ;;
      addInstance (Not i o) ;;
      ret o
  | BufGate => fun i =>
      o <- newWire ;;
      addInstance (Buf i o) ;;
      ret o
  | Uncons n o => fun v => ret ((Vector.hd v, Vector.tl v))
  | Unsnoc n o => fun v => ret (unsnoc v)
  | Primitives.Slice n x y o => fun v => slice' n x y o v
  | Primitives.Split n m o => fun x => ret (Vector.splitat n x)
  | Lut n f => fun is =>
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

  | Primitives.Fst X Y => fun x => ret (fst x)
  | Primitives.Snd _ _ => fun y => ret (snd y)
  end.

Definition binary_primitive_netlist x y z (p: BinaryPrimitive x y z)
  : denote x -> denote y -> state CavaState (denote z) :=
  match p with
  | Primitives.Pair _ _ => fun x y => ret (x,y)
  | Primitives.And => fun x y =>
      o <- newWire ;;
      addInstance (And x y o) ;;
      ret o
  | Primitives.Nand => fun x y =>
      o <- newWire ;;
      addInstance (Nand x y o) ;;
      ret o
  | Primitives.Or => fun x y =>
      o <- newWire ;;
      addInstance (Or x y o) ;;
      ret o
  | Primitives.Nor => fun x y =>
      o <- newWire ;;
      addInstance (Nor x y o) ;;
      ret o
  | Primitives.Xor => fun i0 i1 =>
      o <- newWire ;;
      addInstance (Xor i0 i1 o) ;;
      ret o
  | Primitives.Xnor => fun i0 i1 =>
      o <- newWire ;;
      addInstance (Xnor i0 i1 o) ;;
      ret o
  | Primitives.Xorcy => fun i0 i1 =>
      o <- newWire ;;
      addInstance (Component "XORCY" []
      [("O", USignal o); ("CI", USignal i0); ("LI", USignal i1)]) ;;
      ret o
  | Muxcy => fun s '(ci, di) =>
      o <- newWire ;;
      addInstance ( Component "MUXCY" []
      [("O", USignal o); ("S", USignal s); ("CI", USignal ci); ("DI", USignal di)]) ;;
      ret o
  | Primitives.UnsignedAdd m n s => fun x y =>
      sum <- newVector _ s ;;
      addInstance (UnsignedAdd (VecLit x) (VecLit y) sum) ;;
      ret (Vector.map (IndexConst sum) (vseq 0 s))
  | Primitives.UnsignedSub s => fun x y =>
      sum <- newVector _ s ;;
      addInstance (UnsignedSubtract (VecLit x) (VecLit y) sum) ;;
      ret (Vector.map (IndexConst sum) (vseq 0 s))
  | Index n o => fun x y => index' _ _ x y
  | Primitives.Cons n o => fun x y =>
    ret ((x :: y)%vector)
  | Snoc n o => fun x y => ret (snoc x y)
  | Primitives.Concat n m o => fun x y =>
    ret ((x ++ y)%vector)
  end.

Definition primitive_netlist (p: CircuitPrimitive)
  : denote (primitive_input p) -> state CavaState (denote (primitive_output p)) :=
  match p with
  | P0 p => fun _ => nullary_primitive_netlist _ p
  | P1 p => fun x => unary_primitive_netlist _ _ p x
  | P2 p => fun x => binary_primitive_netlist _ _ _ p (fst x) (snd x)
  end.

Fixpoint build_netlist' {i o}
  (c: Circuit i o)
  : denote i ->
    state CavaState (denote o) :=
    match c as c' in Circuit i' o' return denote i' -> state CavaState (denote o') with
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
      map2M (fun x y => AssignSignal x y) Z z z' ;;
      ret y

  | Loopl _ _ Z f => fun x =>
      z <- fresh_wire Z ;;
      '(z',y) <- (build_netlist' f) (z,x) ;;
      map2M (fun x y => AssignSignal x y) Z z z' ;;
      ret y

  | Delay o => fun x =>
      y <- fresh_wire _ ;;
      map2M (fun x y => DelayBit x y) _ x y ;;
      ret y
  | Primitive p => primitive_netlist p
  | RewriteTy x y => fun v => ret (rewrite_or_default x y v)
end.

Close Scope string_scope.
Local Open Scope category_scope.

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

Definition build_netlist'' {X Y} (circuit: X ~> Y)
  (i: denote (remove_rightmost_unit X))
  : state CavaState (denote Y) :=
  build_netlist' circuit (apply_rightmost_tt X i).

Fixpoint stringify_kind (ty: Kind): Type :=
match ty with
| Tuple l r => prod (stringify_kind l) (stringify_kind r)
| Unit => unit
| Bit => string
| Vector t n => string
end.

Fixpoint make_representable (ty:Kind) :=
match ty with
| Bit => Signal.Bit
| Vector t n => Signal.Vec (make_representable t) n
| _ => Signal.Vec Signal.Bit (packed_width ty)
end.

Fixpoint unpack1 (ty: Kind) (s: Signal (make_representable ty)): denote ty.
Proof.
  destruct ty; cbn in *.

  pose (Vector.map (IndexConst s) (vseq 0 (packed_width ty1 + packed_width ty2))).
  apply (unpack (<<ty1, ty2>>) t).

  exact tt.
  exact s.

  pose (Vector.map (IndexConst s) (vseq 0 n)).
  exact (Vector.map (unpack1 _) t).
Defined.

Fixpoint addInputPorts (ty:Kind) {struct ty}: stringify_kind ty -> state CavaState (denote ty) :=
  match ty as ty' return stringify_kind ty' -> state CavaState (denote ty') with
  | Tuple l r => fun '(lnames, rnames) =>
    l <- addInputPorts l lnames ;;
    r <- addInputPorts r rnames ;;
    ret (l, r)
  | Unit => fun _ => ret tt
  | Bit => fun name =>
    addInputPort (mkPort name Signal.Bit) ;;
    ret (NamedWire name)
  | Vector t n => fun name =>
    addInputPort (mkPort name (Signal.Vec (make_representable t) n)) ;;
    ret (unpack1 (Vector t n) (NamedVector (make_representable t) n name))
  end.

Fixpoint pack_vec (n:nat) (ty: Kind):
  Vector.t (denote ty) n -> Signal (Vec (make_representable ty) n) :=
  match ty as ty return Vector.t (denote ty) n -> Signal (Vec (make_representable ty) n) with
  | Bit => fun v => VecLit v
  | Vector t n => fun v => VecLit (Vector.map (pack_vec n t) v)
  | Unit => fun v => VecLit (Vector.map (fun _ => VecLit []) v)
  | Tuple l r => fun v => VecLit (Vector.map (fun x => VecLit (pack _ x)) v)
  end.

Fixpoint addOutputPorts (ty:Kind) (names: stringify_kind ty) (o: denote ty):
  state CavaState unit :=
  match ty, names, o with
  | Tuple l r, (lnames, rnames), (lo, ro) =>
    addOutputPorts l lnames lo ;;
    addOutputPorts r rnames ro
  | Unit, _, _ => ret tt
  | Bit, name, i =>
    outputBit name i
  | Vector t n, name, i =>
    outputVector (make_representable t) n name (pack_vec _ _ i)
  end.

Definition build_netlist {X Y}
  (circuit: X ~> Y)
  (name: string)
  (inames: stringify_kind (remove_rightmost_unit X))
  (onames: stringify_kind Y)
  : CavaState
  := execState (
    setModuleName name ;;
    setClockAndReset (NamedWire "clk", PositiveEdge) (NamedWire "rst", PositiveEdge) ;;
    addInputPort (mkPort "clk" Signal.Bit) ;;
    addInputPort (mkPort "rst" Signal.Bit) ;;
    i <- addInputPorts (remove_rightmost_unit X) inames ;;
    o <- build_netlist'' circuit i ;;
    addOutputPorts Y onames o
  ) initState.
