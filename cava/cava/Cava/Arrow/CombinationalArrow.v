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
From Cava.Arrow Require Import CavaArrow PropArrow.

Import VectorNotations.
Import EqNotations.

Require Import Cava.BitArithmetic.

(******************************************************************************)
(* Evaluation as function evaluation, no delay elements or loops              *)
(******************************************************************************)

Definition denote_combinational_evaluation {i o} (c: Circuit i o) := denote_kind i -> denote_kind o.

Definition unsnoc' n o (v: denote_kind (Vector o (S n)))
  : (denote_kind (Vector o n) * denote_kind o) :=
  rectS (fun n v => (denote_kind (Vector o n) * denote_kind o)%type)
  (fun o => ([], o))
  (fun o n v f => 
    let '(xs, x) := f in
    (o::xs, x)
  ) v.

Definition snoc' n o (v: denote_kind (Vector o n)) a
  : denote_kind (Vector o (S n)) :=
  t_rect _ (fun n v => denote_kind (Vector o (S n))) [a]
  (fun x n v f => 
    x :: f
  ) _ v.

Definition slice' n x y (o: Kind) (v: denote_kind (Vector o n)) : denote_kind (Vector o (x - y + 1)) := 
  match Nat.eq_dec n (y + (n - y)) with 
  | left Heq =>
    let '(_, v) := splitat y (rew [fun x => Vector.t (denote_kind o) x] Heq in v)
    in 
      match Nat.eq_dec (n-y) ((x - y + 1) + (n - x - 1)) with 
      | left Heq => fst (Vector.splitat (x-y+1) (rew [fun x => Vector.t (denote_kind o) x] Heq in v))
      | right Hneq => kind_default _
      end
  | right Hneq => kind_default _ 
  end.

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

  | Primitive (constant b) => fun _ => b
  | Primitive (constant_bitvec n v) => fun _ => N2Bv_sized n v
  | Primitive (delay_gate o) => fun _ => kind_default _
  | Primitive not_gate => fun b => negb (fst b)
  | Primitive buf_gate => fun b => fst b
  | Primitive (uncons n o) => fun v => (hd (fst v), tl (fst v))
  | Primitive (unsnoc n o) => fun v => unsnoc' n o (fst v)
  | Primitive (split n m o) => fun v => (Vector.splitat n (fst v))
  | Primitive (slice n x y o) => fun v => slice' n x y o (fst v)
  | Primitive (empty_vec o) => fun _ => []
  | Primitive (lut n f) => fun '(i,_) =>
    let f' := NaryFunctions.nuncurry bool bool n f in
    (f' (vec_to_nprod _ _ i))

  | Primitive and_gate => fun '(x,(y,_)) => x && y
  | Primitive nand_gate => fun '(x,(y,_)) => negb ( x && y)
  | Primitive or_gate => fun '(x,(y,_)) => orb x y
  | Primitive nor_gate => fun '(x,(y,_)) => negb (orb x y)
  | Primitive xor_gate => fun '(x,(y,_)) => xorb x y
  | Primitive xnor_gate => fun '(x,(y,_)) => negb (xorb x y)
  | Primitive xorcy => fun '(x,(y,_)) => xorb x y

  | Primitive muxcy => fun i => (if fst i then fst (fst (snd i)) else snd (fst (snd i)))
  | Primitive (unsigned_add m n s) => fun '(av,(bv,_)) =>
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a + b)%N in
    (Ndigits.N2Bv_sized s c)
  | Primitive (unsigned_sub s) => fun '(av, (bv, _)) =>
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a - b)%N in (*todo: This is likely incorrect on underflow *)
    (Ndigits.N2Bv_sized s c)
  | Primitive (index n o) => fun x =>
    match Arith.Compare_dec.lt_dec (bitvec_to_nat (fst (snd x))) n with
    | left Hlt => (nth_order (fst x) Hlt)
    | right Hnlt => kind_default _
    end
  | Primitive (cons n o) => fun '(x, (v,_)) => (x :: v)
  | Primitive (snoc n o) => fun '(v, (x,_)) => snoc' n o v x

  | Primitive (concat n m o) => fun '(x, (y, _)) => Vector.append x y
  end.

Local Open Scope category_scope.

Definition combinational_evaluation {x y: Kind}
  (circuit: x ~> y)
  (ok: is_combinational circuit)
  (i: denote_kind (remove_rightmost_unit x))
  : denote_kind y :=
  combinational_evaluation' (insert_rightmost_tt1 x >>> circuit) i.