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
From Arrow Require Import Category Arrow.
From Cava.Arrow Require Import CircuitArrow.

Import VectorNotations.
Import EqNotations.

Require Import Cava.BitArithmetic.
Require Import Cava.VectorUtils.

(******************************************************************************)
(* Evaluation as function evaluation, no delay elements or loops              *)
(******************************************************************************)

Definition denote_combinational_evaluation {i o} (c: Circuit i o) := denote_kind i -> denote_kind o.

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
  | Primitive (Delay o) => fun _ => kind_default _
  | Primitive Not => fun b => negb (fst b)
  | Primitive BufGate => fun b => fst b
  | Primitive (Uncons n o) => fun v => (hd (fst v), tl (fst v))
  | Primitive (Unsnoc n o) => fun v => vunsnoc (fst v)
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
    match Arith.Compare_dec.lt_dec (bitvec_to_nat (fst (snd x))) n with
    | left Hlt => (nth_order (fst x) Hlt)
    | right Hnlt => kind_default _
    end
  | Primitive (Cons n o) => fun '(x, (v,_)) => (x :: v)
  | Primitive (Snoc n o) => fun '(v, (x,_)) => vsnoc v x

  | Primitive (Concat n m o) => fun '(x, (y, _)) => Vector.append x y

  | Map x y n f => fun v => Vector.map (combinational_evaluation' f) v
  | Resize x n nn => fun v => resize_default (kind_default _) nn v
  end.

Local Open Scope category_scope.

Definition combinational_evaluation {x y: Kind}
  (circuit: x ~> y)
  (i: denote_kind (remove_rightmost_unit x))
  : denote_kind y :=
  combinational_evaluation' circuit (apply_rightmost_tt x i).

