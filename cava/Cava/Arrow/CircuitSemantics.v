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
From Cava Require Import Arrow.Classes.Category.
From Cava Require Import Arrow.Classes.Arrow.
From Cava Require Import Arrow.Classes.Coq.
From Cava Require Import Arrow.Classes.Kleisli.
From Cava Require Import Arrow.CircuitArrow Arrow.ArrowKind Arrow.Primitives.
From Cava Require Import Arrow.ExprLowering.

Import VectorNotations.
Import CategoryNotations.
Import EqNotations.

Require Import Cava.BitArithmetic.
Require Import Cava.VectorUtils.

Local Open Scope category_scope.

Set Typeclasses Unique Solutions.

(******************************************************************************)
(* Evaluation as a Coq function evaluation                                    *)
(******************************************************************************)

Section combinational.
  Definition combinational_category : Category Kind
    := build_denoted_category Kind denote_kind.
  Definition combinational_arrow : Arrow Kind combinational_category Unit Tuple
    := build_denoted_arrow Kind denote_kind Unit Tuple tt
      (fun _ _ => pair)
      (fun _ _ => fst)
      (fun _ _ => snd).

  Instance combinational_drop : Arrows.Drop combinational_arrow := { drop _ _ := tt; }.
  Instance combinational_copy : Arrows.Copy combinational_arrow := { copy _ x := (x,x); }.
  Instance combinational_swap : Arrows.Swap combinational_arrow := { swap _ _ '(x,y) := (y,x); }.
  Instance combinational_arrow_rewrite_or_default
    : Arrows.RewriteOrDefault combinational_arrow := {
    rewrite_or_default := ArrowKind.rewrite_or_default;
  }.

  Instance combinational_annotation : Arrows.Annotation combinational_arrow String.string := {
    annotate _ _ _ f := f
  }.

  Instance combinational_impossible : Arrows.Impossible combinational_arrow := {
    impossible _ _ _ := kind_default _
  }.

  Instance combinational_primitive
    : Arrows.Primitive combinational_arrow CircuitPrimitive primitive_input primitive_output := {
    primitive p := primitive_interp p;
  }.

  Instance combinational_loop : Arrows.Loop combinational_arrow := {
    loopl _ _ _ _ _ := kind_default _;
    loopr _ _ _ _ _ := kind_default _;
  }.

  Instance combinational_circuit : CircuitArrow := {}.

  Definition combinational_evaluation {x y: Kind}
    (circuit: ExprSyntax.Kappa x y)
    (i: denote_kind (remove_rightmost_unit x))
    : denote_kind y :=
    (closure_conversion combinational_circuit circuit) (apply_rightmost_tt x i).
End combinational.

Section sequential.
  Local Notation "'stateless' x => e : k" :=
    ( existT _ Unit (fun x (_ : denote_kind Unit) => (e : denote_kind k, tt : denote_kind Unit)) )
    (at level 1, x pattern, e at level 2 , only parsing ).

  Instance sequential_category : Category Kind := {|
    morphism X Y :=
      { state: Kind & denote_kind X -> denote_kind state -> (denote_kind Y * denote_kind state) };
    id X := stateless x => x : _ ;
    compose X Y Z '(existT _ fk f) '(existT _ gk g) :=
      let state := Tuple gk fk in
      existT _ state
        (fun x (s: denote_kind state) =>
        let '(y, os1) := g x (fst s) in
        let '(z, os2) := f y (snd s) in
        (z, (os1,os2) : denote_kind state)
        );
  |}.

  Instance sequential_arrow : Arrow Kind sequential_category Unit Tuple := {|
    first  X Y Z (f: X ~[sequential_category]~> Y) :=
      match f with
      | existT _ fk f => existT _ fk (fun (x: denote_kind (Tuple X Z)) (s : denote_kind fk) =>
        let '(y, s) := f (fst x) s in
        ((y,snd x),s : denote_kind fk))
      end;
    second X Y Z f :=
      match f with
      | existT _ fk f => existT _ fk (fun (x: denote_kind (Tuple Z X)) (s : denote_kind fk) =>
        let '(y, s) := f (snd x) s in
        ((fst x, y),s : denote_kind fk))
      end;

    assoc   x y z := stateless a => (fst (fst a), (snd (fst a), snd a)) : (Tuple _ (Tuple _ _));
    unassoc x y z := stateless a => ((fst a, fst (snd a)), snd (snd a)) : (Tuple (Tuple _ _) _);

    cancelr x := stateless a => (fst a) : _;
    cancell x := stateless a => (snd a) : _;

    uncancell x := stateless a => (tt, a) : (Tuple Unit _);
    uncancelr x := stateless a => (a, tt) : (Tuple _ Unit);
   |}.

  Instance sequential_drop : Arrows.Drop sequential_arrow :=
    { drop _ := stateless _ => tt : Unit ; }.
  Instance sequential_copy : Arrows.Copy sequential_arrow :=
    { copy _ := stateless x => (x,x) : (Tuple _ _); }.
  Instance sequential_swap : Arrows.Swap sequential_arrow :=
    { swap _ _ := stateless (x,y) => (y,x) : (Tuple _ _); }.

  Instance sequential_arrow_rewrite_or_default : Arrows.RewriteOrDefault sequential_arrow := {
    rewrite_or_default x y :=
      stateless v => (
      match eq_kind_dec x y with
      | left Heq => rew Heq in v
      | right _ => kind_default _
      end) : _ ;
  }.

  Instance sequential_annotation : Arrows.Annotation sequential_arrow String.string := {
    annotate _ _ _ f := f
  }.

  Instance sequential_impossible : Arrows.Impossible sequential_arrow := {
    impossible _ _ := stateless _ => (kind_default _) : _ ;
  }.

  Instance sequential_primitive : Arrows.Primitive sequential_arrow CircuitPrimitive primitive_input primitive_output := {
    primitive p :=
      match p as p' return primitive_input p' ~[ sequential_category ]~> primitive_output p' with
      | Delay o => existT _ o (fun x s => (s, fst x))
      | p => stateless x => (primitive_interp p x) : _
      end;
  }.

  Instance sequential_loop : Arrows.Loop sequential_arrow := {
    loopr X Y Z f :=
      match f with
      | existT _ fk f =>
        existT _ (Tuple fk Z) (
          fun (i: denote_kind X) (s:denote_kind (Tuple fk Z)) =>
            let '(o, ns) := f (i, snd s) (fst s) in
            (fst o : denote_kind Y, (ns, snd o) : denote_kind (Tuple _ _)))
      end;

    loopl X Y Z f :=
      match f with
      | existT _ fk f =>
        existT _ (Tuple Z fk) (
          fun (i: denote_kind X) (s:denote_kind (Tuple Z fk)) =>
            let '(o, ns) := f (fst s, i) (snd s) in
            (snd o : denote_kind Y, (fst o, ns) : denote_kind (Tuple _ _)))
      end;
  }.

  Instance sequential_circuit : CircuitArrow := {
  }.
End sequential.

Definition circuit_evaluation {x y: Kind}
  (circuit: ExprSyntax.Kappa x y)
  : {state: Kind &
    denote_kind (remove_rightmost_unit x) ->
    denote_kind state ->
    denote_kind y * denote_kind state} :=
  match closure_conversion sequential_circuit circuit with
  | existT _ fk f =>
    existT _ fk (
      fun (i: denote_kind (remove_rightmost_unit x)) (s:denote_kind fk) =>
        f (apply_rightmost_tt x i) s)
  end.

