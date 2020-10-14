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

From Coq Require Import Bool ZArith NArith NaryFunctions Vector Lia.
From Cava Require Import Arrow.Classes.Category Arrow.Classes.Arrow.
From Cava Require Import Arrow.CircuitArrow Arrow.ArrowKind Arrow.Primitives.

Import VectorNotations.
Import EqNotations.

Require Import Cava.BitArithmetic.
Require Import Cava.VectorUtils.

(******************************************************************************)
(* Evaluation as function evaluation                                          *)
(******************************************************************************)

Fixpoint combinational_evaluation' {i o}
  (c: Circuit i o)
  : denote_kind i ->
    denote_kind o :=
  match c with
  | Composition _ _ _ f g => fun x =>
    (combinational_evaluation' g) ((combinational_evaluation' f) x)
  | First x y z f => fun x => ((combinational_evaluation' f) (fst x), snd x)
  | Second x y z f => fun x => (fst x, (combinational_evaluation' f) (snd x))
  | Loopr x y z f => fun x => kind_default _
  | Loopl x y z f => fun x => kind_default _

  | Structural (Id _) => fun x => x
  | Structural (Cancelr X) => fun x => fst x
  | Structural (Cancell X) => fun x => snd x
  | Structural (Uncancell _) => fun x => (tt, x)
  | Structural (Uncancelr _) => fun x => (x, tt)
  | Structural (Assoc _ _ _) => fun i => (fst (fst i), (snd (fst i), snd i))
  | Structural (Unassoc _ _ _) => fun i => ((fst i, fst (snd i)), snd (snd i))
  | Structural (Drop x) => fun _ => tt
  | Structural (Swap x y) => fun '(x,y) => (y,x)
  | Structural (Copy x) => fun x => (x,x)

  | Primitive (Constant ty val) => fun _ => val
  | Primitive (ConstantVec n ty val) => fun _ => resize_default (kind_default _) n (Vector.of_list val)
  | Primitive (Delay o) => fun _ => kind_default _
  | Primitive Not => fun b => negb (fst b)
  | Primitive BufGate => fun b => fst b
  | Primitive (Uncons n o) => fun v => (hd (fst v), tl (fst v))
  | Primitive (Unsnoc n o) => fun v => unsnoc (fst v)
  | Primitive (Split n m o) => fun v => (Vector.splitat n (fst v))
  | Primitive (Slice n x y o) => fun v => slice_by_position n x y (kind_default _) (fst v)
  | Primitive (EmptyVec o) => fun _ => []
  | Primitive (Lut n f) => fun '(i,_) =>
    let f' := NaryFunctions.nuncurry bool bool n f in
    (f' (vec_to_nprod _ _ i))

  | Primitive And => fun '(x,(y,_)) => x && y
  | Primitive Nand => fun '(x,(y,_)) => negb ( x && y)
  | Primitive Or => fun '(x,(y,_)) => orb x y
  | Primitive Nor => fun '(x,(y,_)) => negb (orb x y)
  | Primitive Xor => fun '(x,(y,_)) => xorb x y
  | Primitive Xnor => fun '(x,(y,_)) => negb (xorb x y)
  | Primitive Xorcy => fun '(x,(y,_)) => xorb x y

  | Primitive (Fst _ _) => fun '((x,y),_) => x
  | Primitive (Snd _ _) => fun '((x,y),_) => y
  | Primitive (Pair _ _) => fun '(x,(y,_)) => (x,y)

  | Primitive Muxcy => fun i => (if fst i then fst (fst (snd i)) else snd (fst (snd i)))
  | Primitive (UnsignedAdd m n s) => fun '(av,(bv,_)) =>
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a + b)%N in
    (Ndigits.N2Bv_sized s c)
  | Primitive (UnsignedSub s) => fun '(av, (bv, _)) =>
    let a := Z.of_N (Ndigits.Bv2N av) in
    let b := Z.of_N (Ndigits.Bv2N bv) in
    let mod_const := (2^(Z.of_nat s))%Z in
    let c := ((a - b + mod_const) mod mod_const)%Z in
    (Ndigits.N2Bv_sized s (Z.to_N c))
  | Primitive (Index n o) => fun x =>
    nth_default (kind_default _) (bitvec_to_nat (fst (snd x))) (fst x)
  | Primitive (Cons n o) => fun '(x, (v,_)) => (x :: v)
  | Primitive (Snoc n o) => fun '(v, (x,_)) => snoc v x

  | Primitive (Concat n m o) => fun '(x, (y, _)) => Vector.append x y

  | Map x y n f => fun v => Vector.map (combinational_evaluation' f) v
  | Resize x n nn => fun v => resize_default (kind_default _) nn v
  end.

Fixpoint circuit_state {i o} (c: Circuit i o) : Type :=
  match c with
  | Composition _ _ _ f g => prod (circuit_state f) (circuit_state g)
  | First x y z f => circuit_state f
  | Second x y z f => circuit_state f
  | Loopr x y z f => prod (circuit_state f) (denote_kind z)
  | Loopl x y z f => prod (denote_kind z) (circuit_state f)
  | Primitive (Delay o) => denote_kind o
  | Map x y n f => Vector.t (circuit_state f) n
  | _ => Datatypes.unit
  end.

Fixpoint default_state {i o} (c: Circuit i o) : circuit_state c :=
  match c as c' return circuit_state c' with
  | Composition _ _ _ f g => (default_state f, default_state g)
  | First x y z f => default_state f
  | Second x y z f => default_state f
  | Loopr x y z f => (default_state f, kind_default z)
  | Loopl x y z f => (kind_default z, default_state f)
  | Primitive (Delay o) => kind_default o
  | Map x y n f => const (default_state f) _
  | _ => tt
  end.

Fixpoint iterate_looped {i o s} (n: nat)
  (f: denote_kind i -> s -> denote_kind o * s)
  (input: denote_kind i)
  (state: s)
  : denote_kind o * s :=
  let '(o,s) := f input state in
  match n with
  | 0 => (o,s)
  | S n' => iterate_looped n' f input s
  end.

Fixpoint circuit_evaluation' {i o} (n: nat) (c: Circuit i o)
  : denote_kind i -> circuit_state c -> denote_kind o * circuit_state c :=
  match c as c' in Circuit i o
    return denote_kind i -> circuit_state c' -> denote_kind o * circuit_state c'
  with
  | Composition _ _ _ f g => fun x s =>
    let '(y,ls) := circuit_evaluation' n f x (fst s) in
    let '(z,rs) := circuit_evaluation' n g y (snd s) in
    (z, (ls,rs))
  | First x y z f => fun x s =>
    let '(y, ns) := circuit_evaluation' n f (fst x) s in
    ((y,snd x), ns)
  | Second x y z f => fun x s =>
    let '(y, ns) := circuit_evaluation' n f (snd x) s in
    ((fst x,y), ns)
  | Loopr x y z f => fun i s =>
    let '(o,ns) := iterate_looped n (circuit_evaluation' n f) (i, snd s) (fst s) in
    (fst o, (ns, snd o))
  | Loopl x y z f => fun i s =>
    let '(o,ns) := iterate_looped n (circuit_evaluation' n f) (fst s, i) (snd s) in
    (snd o, (fst o, ns))
  | Structural (Id _) => fun x _ => (x, tt)
  | Structural (Cancelr X) => fun x _ => (fst x, tt)
  | Structural (Cancell X) => fun x _ => (snd x, tt)
  | Structural (Uncancell _) => fun x _ => ((tt, x), tt)
  | Structural (Uncancelr _) => fun x _ => ((x, tt), tt)
  | Structural (Assoc _ _ _) => fun i _ => ((fst (fst i), (snd (fst i), snd i)), tt)
  | Structural (Unassoc _ _ _) => fun i _ => (((fst i, fst (snd i)), snd (snd i)), tt)
  | Structural (Drop x) => fun _ _ => (tt, tt)
  | Structural (Swap x y) => fun '(x,y) _ => ((y,x), tt)
  | Structural (Copy x) => fun x _ => ((x,x),tt)

  | Primitive (Constant ty val) => fun _ _ => (val, tt)
  | Primitive (ConstantVec n ty val) => fun _ _ => (resize_default (kind_default _) n (Vector.of_list val), tt)
  | Primitive (Delay o) => fun x s => (s, fst x)
  | Primitive Not => fun b _ => (negb (fst b), tt)
  | Primitive BufGate => fun b _ => (fst b, tt)
  | Primitive (Uncons n o) => fun v _ => (hd (fst v), tl (fst v), tt)
  | Primitive (Unsnoc n o) => fun v _ => (unsnoc (fst v), tt)
  | Primitive (Split n m o) => fun v _ => (Vector.splitat n (fst v), tt)
  | Primitive (Slice n x y o) => fun v _ => (slice_by_position n x y (kind_default _) (fst v), tt)
  | Primitive (EmptyVec o) => fun _ _ => ([], tt)
  | Primitive (Lut n f) => fun '(i,_) _ =>
    let f' := NaryFunctions.nuncurry bool bool n f in
    (f' (vec_to_nprod _ _ i), tt)

  | Primitive And => fun '(x,(y,_)) _ => (x && y, tt)
  | Primitive Nand => fun '(x,(y,_)) _ => (negb ( x && y), tt)
  | Primitive Or => fun '(x,(y,_)) _ => (orb x y, tt)
  | Primitive Nor => fun '(x,(y,_)) _ => (negb (orb x y), tt)
  | Primitive Xor => fun '(x,(y,_)) _ => (xorb x y, tt)
  | Primitive Xnor => fun '(x,(y,_)) _ => (negb (xorb x y), tt)
  | Primitive Xorcy => fun '(x,(y,_)) _ => (xorb x y, tt)

  | Primitive (Fst _ _) => fun '((x,y),_) _ => (x, tt)
  | Primitive (Snd _ _) => fun '((x,y),_) _ => (y, tt)
  | Primitive (Pair _ _) => fun '(x,(y,_)) _ => ((x,y), tt)

  | Primitive Muxcy => fun i _ => (if fst i then fst (fst (snd i)) else snd (fst (snd i)), tt)
  | Primitive (UnsignedAdd m n s) => fun '(av,(bv,_)) _ =>
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a + b)%N in
    (Ndigits.N2Bv_sized s c, tt)
  | Primitive (UnsignedSub s) => fun '(av, (bv, _)) _ =>
    let a := Z.of_N (Ndigits.Bv2N av) in
    let b := Z.of_N (Ndigits.Bv2N bv) in
    let mod_const := (2^(Z.of_nat s))%Z in
    let c := ((a - b + mod_const) mod mod_const)%Z in
    (Ndigits.N2Bv_sized s (Z.to_N c), tt)
  | Primitive (Index n o) => fun x _ =>
    (nth_default (kind_default _)
      (bitvec_to_nat (fst (snd x)))
      (fst x), tt)
  | Primitive (Cons n o) => fun '(x, (v,_)) _ => (x :: v, tt)
  | Primitive (Snoc n o) => fun '(v, (x,_)) _ => (snoc v x, tt)

  | Primitive (Concat n m o) => fun '(x, (y, _)) _ => (Vector.append x y, tt)

  | Map x y n f => fun v s => separate (Vector.map2 (circuit_evaluation' n f) v s)
  | Resize x n nn => fun v _ => (resize_default (kind_default _) nn v, tt)
  end.

Local Open Scope category_scope.

Definition combinational_evaluation {x y: Kind}
  (circuit: x ~> y)
  (i: denote_kind (remove_rightmost_unit x))
  : denote_kind y :=
  combinational_evaluation' circuit (apply_rightmost_tt x i).

Definition circuit_evaluation {x y: Kind} (n: nat)
  (circuit: x ~> y)
  (i: denote_kind (remove_rightmost_unit x))
  (state: circuit_state circuit)
  : (denote_kind y * circuit_state circuit) :=
  circuit_evaluation' n circuit (apply_rightmost_tt x i) state.

