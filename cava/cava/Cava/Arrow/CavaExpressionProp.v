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

(* temporarily disabled *)
From Arrow Require Import Category Arrow Kappa KappaProp KappaEquiv ClosureConversion.
From Cava Require Import Arrow.CavaArrow Arrow.CavaExpression.
(* From Cava Require Import Arrow.CavaArrow Arrow.EvaluationArrow Arrow.CavaExpression. *)

From Coq Require Import Arith NArith Lia NaryFunctions.

Import EqNotations.

Open Scope category_scope.
Open Scope arrow_scope.

(* TODO: This is defined in the standard library but P is restricted to `A -> Prop`:
  upstream fix to github.com/coq/coq *)
Lemma rew_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Type) (u : { p : P x & Q x p }) {y} (H : x = y)
    : rew [fun a => { p : P a & Q a p }] H in u
      = existT
          (Q y)
          (rew H in projT1 u)
          (match H with 
          | eq_refl => projT2 u
          end).
Proof.
  destruct H, u; reflexivity.
Qed.

(* TODO(blaxill): remove axiom *)
(* Axiom no_let_rec_and_stateless_morphisms_is_stateless:
  forall i o (expr: Kappa i o) env wf, 
    no_letrec (expr _) = true ->
    morph_prop (fun _ _ m => has_no_state m) (expr _) ->
    has_no_state ((fun (cava: Cava) => closure_conversion' env (expr _) wf) EvalCava). *)

(* proof broken by changes *)
(* Lemma no_let_rec_and_stateless_morphisms_is_stateless:
  forall i o (expr: Kappa i o) env wf, 
    no_letrec (expr _) = true ->
    morph_prop (fun _ _ m => has_no_state m) (expr _) ->
    has_no_state ((fun (cava: Cava) => closure_conversion' env (expr _) wf) EvalCava).
*)

(* Hint Extern 15 => apply (no_let_rec_and_stateless_morphisms_is_stateless _ _) : stateless. *)
(* Hint Extern 20 => refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _ ) : stateless. *)