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

From Coq Require Import Arith.Arith NArith.NArith micromega.Lia
     Numbers.NaryFunctions Lists.List.

From Cava Require Import Arrow.Classes.Category.
From Cava Require Import Arrow.Classes.Arrow.
From Cava Require Import Arrow.CircuitArrow.
From Cava Require Import Arrow.CircuitSemantics.
From Cava Require Import Arrow.ExprSyntax.
From Cava Require Import Arrow.ExprLowering.
From Cava Require Import Arrow.ArrowKind.
From Cava Require Import Arrow.Primitives.

Import EqNotations.
Import ListNotations.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

From ExtLib Require Import Structures.Monads.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Traversable.
From ExtLib Require Export Data.Monads.StateMonad.

Import MonadNotation.

Section combinational_semantics.
  Definition coq_func t := denote_kind t.

  Fixpoint interp_combinational' {i o: Kind}
    (expr: kappa coq_func i o)
    : denote_kind i -> denote_kind o :=
    match expr with
    | Var x => fun v : unit => x
    | Abs f => fun '(x,y) => interp_combinational' (f x) y
    | App f e => fun y =>
      (interp_combinational' f) (interp_combinational' e tt, y)
    | Comp g f => fun x => interp_combinational' g (interp_combinational' f x)
    | Comp1 g f => fun x => interp_combinational' g (denote_apply_rightmost_tt _ (interp_combinational' f x))
    | Primitive p =>
      match p with
      | P0 p => primitive_semantics (P0 p)
      | P1 p => fun x => primitive_semantics (P1 p) (fst x)
      | P2 p => fun x => primitive_semantics (P2 p) (fst x, fst (snd x))
      end
    | Id => fun x => x
    | Typecast _ _ => rewrite_or_default _ _
    | Let v f => fun y =>
      interp_combinational' (f (interp_combinational' v tt)) y
    | CallModule (mkModule _ m) => interp_combinational' (m _)

    | LetRec v f => fun _ => kind_default _
    | Delay => fun _ => kind_default _
    end.

  Definition interp_combinational {x y: Kind}
    (expr: kappa coq_func x y)
    (i: denote_kind (remove_rightmost_unit x)): (denote_kind y) :=
    interp_combinational' expr (denote_apply_rightmost_tt x i).

  Definition list_func t := list (denote_kind t).

  Fixpoint interp_sequential' {i o: Kind}
    (expr: kappa list_func i o)
    : list_func i -> list_func o :=
    match expr in kappa _ i o return list_func i -> list_func o with
    | Var x => fun v : list unit => x
    | Abs f => fun xy =>
      let '(x,y) := split xy in interp_sequential' (f x) y
    | App f e => fun y =>
      (interp_sequential' f) (combine (interp_sequential' e (repeat tt (length y))) y)
    | Comp g f => fun x => interp_sequential' g (interp_sequential' f x)
    | Comp1 g f => fun x => interp_sequential' g (map (denote_apply_rightmost_tt _) (interp_sequential' f x))
    | Primitive p =>
      match p with
      | P0 p => fun x => map (fun x => primitive_semantics (P0 p) x) x
      | P1 p => fun x => map (fun x => primitive_semantics (P1 p) (fst x)) x
      | P2 p => fun x => map (fun x => primitive_semantics (P2 p) (fst x, fst (snd x))) x
      end
    | Id => fun x => x
    | Typecast _ _ => map (rewrite_or_default _ _)
    | Let v f => fun y =>
      interp_sequential' (f (interp_sequential' v (repeat tt (length y)))) y
    | CallModule (mkModule _ m) => interp_sequential' (m _)

    | LetRec v f => fun y =>
      (* TODO(#_): fixme: this has terrible performance as it each item requires
        resimulatution of previous steps for subcircuit.
        Is there a performant simple way to write this?
        Single cycle step semantics bypasses this issue (see unroll_circuit_evaluation)
      *)
      let vs := fold_left
        (fun vs t => kind_default _ :: interp_sequential' (v vs) (repeat tt t))
        (repeat (length y) (length y)) [] in
      interp_sequential' (f vs) y

    | Delay => fun x => kind_default _ :: map fst x
    end.

  Definition interp_sequential {x y: Kind}
    (expr: kappa list_func x y)
    (i: list_func (remove_rightmost_unit x)): (list_func y) :=
    interp_sequential' expr (map (denote_apply_rightmost_tt x) i).

  Inductive skappa: Kind -> Kind -> Type :=
  | SVar : forall {x}, nat -> skappa Unit x
  | SAbs : forall {x y z}, skappa y z -> skappa (Tuple x y) z
  | SApp : forall {x y z}, skappa (Tuple x y) z -> skappa Unit x -> skappa y z
  | SComp: forall {x y z}, skappa y z -> skappa x y -> skappa x z
  | SComp1: forall {x y z}, skappa y z -> skappa x (remove_rightmost_unit y) -> skappa x z
  | SDelay: forall {x},
    skappa (Tuple x Unit) x
  | SPrimitive : forall prim, skappa (extended_prim_input prim) (primitive_output prim)
  | SLet: forall {x y z}, skappa Unit x -> skappa y z -> skappa y z
  | SLetRec : forall {x y z},
    skappa Unit x -> skappa y z -> skappa y z
  | SId : forall {x}, skappa x x
  | STypecast : forall x y, skappa (Tuple x Unit) y
  | SCallModule: forall {x y}, skappa x y -> skappa x y
  .

  Arguments skappa : clear implicits.

  Print skappa.

  Fixpoint to_skappa {i o} (n: nat) (e: kappa natvar i o): skappa i o :=
    match e with
    | Var x => SVar x
    | Abs f => SAbs (to_skappa (S n) (f n))
    | App f e => SApp (to_skappa n f) (to_skappa n e)
    | Comp f g => SComp (to_skappa n f) (to_skappa n g)
    | Comp1 f g => SComp1 (to_skappa n f) (to_skappa n g)
    | Delay => SDelay
    | Let v f => SLet (to_skappa n v) (to_skappa (S n) (f n))
    | LetRec v f =>
      SLetRec
        (to_skappa (S n) (v n))
        (to_skappa (S n) (f n))
    | Id => SId
    | Typecast _ _ => STypecast _ _
    | CallModule (mkModule _ m) => SCallModule (to_skappa 0 (m _))
    | Primitive p => SPrimitive p
    end.

  Definition to_skappa' {i o} (e: Kappa i o): skappa i o :=
    to_skappa 0 (e _).

  Definition merge_maybes (a b: option Type): option Type :=
    match a, b with
    | Some a, Some b => Some (prod a b)
    | Some a, _ => Some a
    | _, Some b => Some b
    | _, _ => None
    end.

  Fixpoint skappa_state {i o} (e: skappa i o): Type :=
    match e with
    | SAbs f => skappa_state f
    | SApp f e => prod (skappa_state f) (skappa_state e)
    | SComp f g => prod (skappa_state f) (skappa_state g)
    | SComp1 f g => prod (skappa_state f) (skappa_state g)
    | @SDelay x => denote_kind x
    | SLet v f => prod (skappa_state v) (skappa_state f)
    | @SLetRec x _ _ v f =>
      (prod (denote_kind x) (prod (skappa_state v) (skappa_state f)))
    | SCallModule e => skappa_state e
    | _ => unit
    end.

  Definition index_env (env: list {x&denote_kind x}) (n: nat) (x: Kind)
    : denote_kind x :=
    match nth_error env n with
    | None => kind_default _
    | Some (existT _ k v) => rewrite_or_default _ _ v
    end.

  Notation "x :< y" := (y ++ [existT _ _ x]) (at level 0, no associativity).

  Fixpoint sequential_step {i o} (e: skappa i o)
    (env: list {x&denote_kind x}) :
    skappa_state e -> denote_kind i ->
    (skappa_state e * denote_kind o)
    :=
    match e as e in skappa i o return
      skappa_state e -> denote_kind i ->
      (skappa_state e * denote_kind o)
      with
    | SVar n => fun _ _ => (tt, index_env env n _)
    | SAbs f =>
      fun s '(x,y) => sequential_step f (x :< env) s y
    | SApp f e =>
      fun s x =>
        let '(os2, y) := sequential_step e env (snd s) tt in
        let '(os1, z) := sequential_step f env (fst s) (y, x) in
        ((os1,os2), z)
    | SComp f g =>
      fun s x =>
        let '(os2, y) := sequential_step g env (snd s) x in
        let '(os1, z) := sequential_step f env (fst s) y in
        ((os1,os2), z)
    | SComp1 f g =>
      fun s x =>
        let '(os2, y) := sequential_step g env (snd s) x in
        let '(os1, z) := sequential_step f env (fst s) (denote_apply_rightmost_tt _ y) in
        ((os1,os2), z)
    | @SDelay x => fun s '(i,_) => (i, s)
    | SLet v f =>
      fun s x =>
        let '(os1, y) := sequential_step v env (fst s) tt in
        let '(os2, z) := sequential_step f (y :< env) (snd s) x in
        ((os1,os2), z)
    | @SLetRec x _ _ v f =>
      fun  s
      (* '(sv, (s1,s2)) *)
      x =>
        let '(os1, y) := sequential_step v ((fst s) :< env) (fst (snd s)) tt in
        let '(os2, z) := sequential_step f ((fst s) :< env) (snd (snd s)) x in
        ((y,(os1,os2)), z)
    | SCallModule e => fun s i => sequential_step e [] s i
    | SId => fun _ x => (tt, x)
    | STypecast _ _ => fun _ x => (tt, rewrite_or_default _ _ x)
    | SPrimitive p =>
      match p with
      | P0 p => fun _ x => (tt, primitive_semantics (P0 p) x)
      | P1 p => fun _ x => (tt, primitive_semantics (P1 p) (fst x))
      | P2 p => fun _ x => (tt, primitive_semantics (P2 p) (fst x, fst (snd x)))
      end
    end.

  Fixpoint wf_indexing {i o}
  (ctxt: list Kind)
  (expr: skappa i o) {struct expr}
  : Prop :=
  match expr with
  | SVar n  => nth_error ctxt n = Some o
  | @SAbs x _ _ f => wf_indexing (ctxt ++ [x]) f
  | SApp e1 e2 => wf_indexing ctxt e1 /\ wf_indexing ctxt e2
  | SComp e1 e2 => wf_indexing ctxt e1 /\ wf_indexing ctxt e2
  | SComp1 e1 e2 => wf_indexing ctxt e1 /\ wf_indexing ctxt e2
  | SDelay => True
  | SPrimitive _ => True
  | SId => True
  | STypecast x y => True
  | @SLet x _ _ v f => wf_indexing (ctxt ++ [x]) f /\ wf_indexing ctxt v
  | @SLetRec x _ _ v f => wf_indexing (ctxt ++ [x]) v/\ wf_indexing (ctxt ++ [x]) f
  | SCallModule e => wf_indexing [] e
  end.

  Fixpoint sequential_step' {i o} (e: skappa i o):
    skappa_state e -> denote_kind i ->
    (skappa_state e * denote_kind o)
    := sequential_step e [].

  Fixpoint unroll_sequential_step' {i o: Kind}
    (e: skappa i o)
    (state: skappa_state e)
    (i: list (denote_kind (remove_rightmost_unit i)))
    : list (denote_kind o) :=
    match i with
    | [] => []
    | x :: xs =>
      let '(ns, o) := sequential_step' e state (denote_apply_rightmost_tt _ x)
      in o :: unroll_sequential_step' e ns xs
    end%list.

  Fixpoint default_state {i o} (e: skappa i o) : skappa_state e :=
    match e with
    | SAbs f => default_state f
    | SApp f e => pair (default_state f) (default_state e)
    | SComp f g => pair (default_state f) (default_state g)
    | SComp1 f g => pair (default_state f) (default_state g)
    | @SDelay x => kind_default x
    | SLet v f => pair (default_state v) (default_state f)
    | @SLetRec x _ _ v f =>
      (pair (kind_default x) (pair (default_state v) (default_state f)))
    | SCallModule e => default_state e
    | _ => tt
    end.

  Definition unroll_sequential_step {i o: Kind}
    (e: skappa i o)
    (i: list (denote_kind (remove_rightmost_unit i)))
    : list (denote_kind o) :=
    unroll_sequential_step' e (default_state _) i.

  Lemma next_sequential_step {x y} (e: skappa x y) s i is :
    unroll_sequential_step' e s (i::is) =
      let '(ns, o) := sequential_step' e s (denote_apply_rightmost_tt _ i)
      in o :: unroll_sequential_step' e ns is.
  Proof. auto. Qed.

End combinational_semantics.

(* convenient notation *)
Notation kinterp x := (interp_combinational' ((x: Kappa _ _) coq_func)).
