(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Cava.Util.List. (* TODO: From cava 1 *)

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.

Local Open Scope circuit_type_scope.

Definition split_absorbed_denotation {x y}
  : denote_type (x ++ y) -> denote_type x * denote_type y :=
  match x, y with
  | [],_ => fun x => (tt,x)
  | _,[] => fun x => (x, tt)
  | _, _ => fun x => x
  end.

Definition combine_absorbed_denotation {x y}
  : denote_type x -> denote_type y -> denote_type (x ++ y) :=
  match x,y with
  | [], _ => fun _ y => y
  | _, [] => fun x _ => x
  | _, _ => fun x y => (x,y)
  end.

Fixpoint step {i s o} (c : Circuit s i o)
  : denote_type s -> denote_type i -> denote_type s * denote_type o :=
  match c in Circuit s i o return denote_type s -> denote_type i -> denote_type s * denote_type o with
  | Var x => fun _ _ => (tt, x)
  | Abs f => fun s '(i1,i2) =>
    step (f i1) s i2
  | App f x => fun s i =>
    let '(sx, sf) := split_absorbed_denotation s in
    let '(nsx, x) := step x sx tt in
    let '(nsf, o) := step f sf (x, i) in
    (combine_absorbed_denotation nsx nsf, o)
  | Delay _ => fun s '(i,tt) => (i, s)
  | Let x f => fun s i =>
    let '(sx, sf) := split_absorbed_denotation s in
    let '(nsx, x) := step x sx tt in
    let '(nsf, o) := step (f x) sf i in
    (combine_absorbed_denotation nsx nsf, o)
  | LetDelay _ x f => fun s i =>
    let '(sx, s12) := split_absorbed_denotation s in
    let '(s1, s2) := split_absorbed_denotation s12 in

    let '(ns1, x) := step (x sx) s1 tt in
    let '(ns2, o) := step (f x) s2 i in

    (combine_absorbed_denotation x (combine_absorbed_denotation ns1 ns2), o)

  | ElimPair f (x,y) => fun s i =>
    let '(ns, o) := step (f x y) s i in
    (ns, o)
  | ElimBool b f g => fun s i =>
    let '(_, bv) := step b tt tt in
    let '(sf, sg) := split_absorbed_denotation s in
    let '(nsf, fo) := step f sf tt in
    let '(nsg, go) := step g sg tt in
    (combine_absorbed_denotation nsf nsg, if bv then fo else go)

  | MakePair f g => fun s _ =>
    let '(sf, sg) := split_absorbed_denotation s in
    let '(nsf, x) := step f sf tt in
    let '(nsg, y) := step g sg tt in
    (combine_absorbed_denotation nsf nsg, (x,y))
  | Constant _ v => fun _ _ => (tt, v)
  | UnaryOp op x => fun _ _ => (tt, unary_semantics op x)
  | BinaryOp op x y => fun _ _ => (tt, binary_semantics op x y)
  | TernaryOp op x y z => fun _ _ => (tt, ternary_semantics op x y z)
  end.

Fixpoint reset_state {i s o} (c : Circuit (var:=denote_type) s i o) : denote_type s :=
  match c in Circuit s i o return denote_type s with
  | Var _ => tt
  | Abs f => reset_state (f default)
  | App f x => combine_absorbed_denotation (reset_state x) (reset_state f)
  | Let x f => combine_absorbed_denotation (reset_state x) (reset_state (f default))
  | LetDelay initial x f =>
    combine_absorbed_denotation initial
      (combine_absorbed_denotation (reset_state (x default)) (reset_state (f default)))
  | Delay initial => initial
  | MakePair f g => combine_absorbed_denotation (reset_state f) (reset_state g)
  | Constant _ _ => tt
  | ElimPair f _ =>  reset_state (f default default)
  | ElimBool b f g => combine_absorbed_denotation (reset_state f) (reset_state g)
  | UnaryOp op x => tt
  | BinaryOp op x y => tt
  | TernaryOp op x y z => tt
  end.

Definition simulate' {s i o} (c : Circuit (var:=denote_type) s i o) (input : list (denote_type i)) (state: denote_type s)
  : list (denote_type o) * denote_type s :=
    fold_left_accumulate' (step c) nil input state.

Definition simulate {s i o} (c : Circuit (var:=denote_type) s i o) (input : list (denote_type i))
  : list (denote_type o) := fst (simulate' c input (reset_state c)).
