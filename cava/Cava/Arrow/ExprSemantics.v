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

Require Import Coq.Arith.Arith
     Coq.Lists.List.
Require Import Cava.Arrow.ExprSyntax.
Require Import Cava.Arrow.Primitives.

Import EqNotations.
Import ListNotations.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

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
      let vs := tl (
        fold_left
        (fun vs t => kind_default _ :: interp_sequential' (v vs) (repeat tt t))
        (seq 0 (S (length y))) []) in

      interp_sequential' (f vs) y

    | Delay => fun x => kind_default _ :: map fst x
    end.

  Definition interp_sequential {x y: Kind}
    (expr: kappa list_func x y)
    (i: list_func (remove_rightmost_unit x)): (list_func y) :=
    interp_sequential' expr (map (denote_apply_rightmost_tt x) i).

  Notation state := (list {k & denote_kind k}).

  Fixpoint interp_sequential1' {i o: Kind}
    (expr: kappa coq_func i o)
    : state -> denote_kind i -> (state * state * denote_kind o) :=
    match expr in kappa _ i o return state -> denote_kind i -> (state * state * denote_kind o) with
    | Abs f => fun s '(x,y) => interp_sequential1' (f x) s y
    | App f e => fun s y =>
      let '(state_curr, state_next1, o) := interp_sequential1' e s tt in
      let '(state_curr, state_next2, o) := interp_sequential1' f state_curr (o, y) in
      (state_curr, state_next1 ++ state_next2, o)
    | Comp g f => fun s x =>
      let '(state_curr, state_next1, o) := interp_sequential1' f s x in
      let '(state_curr, state_next2, o) := interp_sequential1' g state_curr o in
      (state_curr, state_next1 ++ state_next2, o)
    | Comp1 g f => fun s x =>
      let '(state_curr, state_next1, o) := interp_sequential1' f s x in
      let '(state_curr, state_next2, o) := interp_sequential1' g state_curr (denote_apply_rightmost_tt _ o) in
      (state_curr, state_next1 ++ state_next2, o)
    | CallModule (mkModule _ m) => interp_sequential1' (m _)

    | Let v f => fun s y =>
      let '(state_curr, state_next1, o) := interp_sequential1' v s tt in
      let '(state_curr, state_next2, o) := interp_sequential1' (f o) state_curr y in
      (state_curr, state_next1 ++ state_next2, o)
    | LetRec v f => fun s x =>
      let '(state_curr, old_v) :=
        match s with
        | [] => ([], kind_default _)
        | existT _ _ s :: ss => (ss, rewrite_or_default _ _ s)
        end in
      let '(state_curr, state_next1, next_v) := interp_sequential1' (v old_v) state_curr tt in
      let '(state_curr, state_next2, o) := interp_sequential1' (f next_v) state_curr x in
      (state_curr, [existT _ _ next_v] ++ state_next1 ++ state_next2, o)

    | @Delay _ X => fun s '(x,_) =>
      match s with
      | [] => ([], [existT _ X x], kind_default _)
      | existT _ _ s :: ss =>
        (ss, [existT _ X x], rewrite_or_default _ _ s)
      end

    | e => fun s x => (s, [], interp_combinational' e x)
    end.

  Definition interp_sequential1 {x y: Kind}
    (expr: kappa coq_func x y)
    (s: state)
    (i: coq_func (remove_rightmost_unit x)): (state * coq_func y) :=
    let '(_, s, o) := interp_sequential1' expr s (denote_apply_rightmost_tt x i) in
    (s, o).

  Definition interp_sequential11 {x y: Kind}
    (expr: kappa coq_func x y)
    (i: list_func (remove_rightmost_unit x)): (list_func y) :=
    snd (
    fold_left (fun '(s, os) i =>
      let (ns, o) := interp_sequential1 expr (rev s) i in
      (ns, os ++ [o])
    ) i ([], []) ).

End combinational_semantics.

(* convenient notation *)
Notation kinterp x := (interp_combinational' ((x: Kappa _ _) coq_func)).
