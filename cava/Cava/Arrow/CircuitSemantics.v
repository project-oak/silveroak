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

From Coq Require Import Bool ZArith NArith NaryFunctions Vector Lia List.
From Cava Require Import Arrow.Classes.Category Arrow.Classes.Arrow.
From Cava Require Import Arrow.CircuitArrow Arrow.ArrowKind Arrow.Primitives.

Import ListNotations.
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

  | Primitive p => primitive_interp p
  | RewriteTy x y => rewrite_or_default x y

  end.

Fixpoint circuit_state {i o} (c: Circuit i o) : Type :=
  match c with
  | Composition _ _ _ f g => prod (circuit_state f) (circuit_state g)
  | First x y z f => circuit_state f
  | Second x y z f => circuit_state f
  | Loopr x y z f => circuit_state f
  | Loopl x y z f => circuit_state f
  | Primitive (Delay o) => denote_kind o
  | _ => Datatypes.unit
  end.

Fixpoint default_state {i o} (c: Circuit i o) : circuit_state c :=
  match c as c' return circuit_state c' with
  | Composition _ _ _ f g => (default_state f, default_state g)
  | First x y z f => default_state f
  | Second x y z f => default_state f
  | Loopr x y z f => default_state f
  | Loopl x y z f => default_state f
  | Primitive (Delay o) => kind_default o
  | _ => tt
  end.

Fixpoint circuit_evaluation' {i o} (c: Circuit i o)
  : denote_kind i -> circuit_state c -> denote_kind o * circuit_state c :=
  match c as c' in Circuit i o
    return denote_kind i -> circuit_state c' -> denote_kind o * circuit_state c'
  with
  | Composition _ _ _ f g => fun x s =>
    let '(y,ls) := circuit_evaluation' f x (fst s) in
    let '(z,rs) := circuit_evaluation' g y (snd s) in
    (z, (ls,rs))
  | First x y z f => fun x s =>
    let '(y, ns) := circuit_evaluation' f (fst x) s in
    ((y,snd x), ns)
  | Second x y z f => fun x s =>
    let '(y, ns) := circuit_evaluation' f (snd x) s in
    ((fst x,y), ns)

  | Loopr x y z f => fun i s =>
    (* Run once with default input but correct state to get our input Z values out,
    this is valid if every path x*z~>z is buffered *)
    let '((_,zs),_) := circuit_evaluation' f (kind_default _) s in
    let '((o,_),s) := circuit_evaluation' f (i,zs) s in (o,s)
  | Loopl x y z f => fun i s =>
    (* ditto as above *)
    let '((zs,_),_) := circuit_evaluation' f (kind_default _) s in
    let '((_,o),s) := circuit_evaluation' f (zs,i) s in (o,s)
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

  | Primitive (Delay o) => fun x s => (s, fst x)
  | Primitive p => fun x _ => (primitive_interp p x, tt)

  | RewriteTy x y => fun v _ => (rewrite_or_default x y v, tt)
  end.

Local Open Scope category_scope.

Definition combinational_evaluation {x y: Kind}
  (circuit: x ~> y)
  (i: denote_kind (remove_rightmost_unit x))
  : denote_kind y :=
  combinational_evaluation' circuit (apply_rightmost_tt x i).

Definition circuit_evaluation {x y: Kind}
  (circuit: x ~> y)
  (i: denote_kind (remove_rightmost_unit x))
  (state: circuit_state circuit)
  : (denote_kind y * circuit_state circuit) :=
  circuit_evaluation' circuit (apply_rightmost_tt x i) state.

Fixpoint unroll_circuit_evaluation' {x y: Kind}
  (circuit: x ~> y)
  (state: circuit_state circuit)
  (i: list (denote_kind (remove_rightmost_unit x)))
  : list (denote_kind y) :=
  match i with
  | [] => []
  | x :: xs =>
    let '(o,ns) := circuit_evaluation circuit x state
    in o :: unroll_circuit_evaluation' circuit ns xs
  end%list.

Definition unroll_circuit_evaluation {x y: Kind}
  (circuit: x ~> y)
  (i: list (denote_kind (remove_rightmost_unit x)))
  : list (denote_kind y) :=
  unroll_circuit_evaluation' circuit (default_state _) i.

