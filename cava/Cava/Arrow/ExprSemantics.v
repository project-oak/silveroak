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

From Cava Require Import Arrow.Classes.Category.
From Cava Require Import Arrow.Classes.Arrow.
From Cava Require Import Arrow.CircuitArrow.
From Cava Require Import Arrow.CircuitSemantics.
From Cava Require Import Arrow.ExprSyntax.
From Cava Require Import Arrow.ExprLowering.
From Cava Require Import Arrow.ArrowKind.
From Cava Require Import Arrow.Primitives.

From Coq Require Import Arith NArith Lia NaryFunctions.

Import EqNotations.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

Section combinational_semantics.
  Definition coq_func t := denote_kind t.

  Fixpoint interp_combinational' {i o: Kind}
    (expr: kappa coq_func i o)
    : denote_kind i -> (denote_kind o) :=
    match expr in kappa _ i0 o0 return denote_kind i0 -> denote_kind o0 with
    | Var x => fun v : unit => x
    | Abs f => fun '(x,y) => interp_combinational' (f x) y
    | App f e => fun y =>
      (interp_combinational' f) (interp_combinational' e tt, y)
    | Comp g f => fun x => interp_combinational' g (interp_combinational' f x)
    | Primitive p => primitive_interp p
    | Id => fun x => x
    | Let v f => fun y =>
      interp_combinational' (f (interp_combinational' v tt)) y
    | LetRec v f => fun _ => kind_default _
    | RemoveContext f => interp_combinational' f
    end.

  Definition interp_combinational {x y: Kind}
    (expr: kappa coq_func x y)
    (i: denote_kind (remove_rightmost_unit x)): (denote_kind y) :=
    interp_combinational' expr (apply_rightmost_tt x i).

  Axiom expression_evaluation_is_arrow_evaluation: forall i o (expr: Kappa i o), forall (x: denote_kind i),
    combinational_evaluation' (closure_conversion expr) x =
    interp_combinational' (expr _) x.

End combinational_semantics.
