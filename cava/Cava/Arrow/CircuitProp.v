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

From Coq Require Import Bool ZArith NaryFunctions Vector.
Require Import coqutil.Tactics.Tactics.
From Cava Require Import Arrow.Classes.Category.
From Cava Require Import Arrow.Classes.Arrow.
From Cava Require Import Arrow.CircuitArrow Arrow.CircuitSemantics.
From Cava Require Import Arrow.ArrowKind Arrow.Primitives.
From Cava Require Import Arrow.ExprSyntax.
From Cava Require Import Arrow.ExprLowering.
From Cava Require Import Arrow.ExprLoweringPreservation.
From Cava Require Import Arrow.ExprEquiv.
From Cava Require Import Arrow.ExprSemantics.

From ExtLib Require Import Structures.Monoid.
Import VectorNotations.

Section combinational.
  From Cava Require Import Arrow.Classes.Monoid.
  Local Notation all := (monoid_arrow Kind bool all_monoid Unit Tuple).
  Instance no_loops_loop : Arrows.Loop all := {
    loopl _ _ _ _ := false;
    loopr _ _ _ _ := false;
  }.

  Instance no_delays_primitives
    : Arrows.Primitive all
      CircuitPrimitive primitive_input primitive_output := {
    primitive p :=
      match p with
      | Delay _ => false
      | _ => true
      end;
  }.

  Instance is_combinational_circuit : CircuitArrow := {}.
End combinational.

Definition is_combinational {i o: Kind}
  (circuit: ExprSyntax.Kappa i o) :=
  (closure_conversion is_combinational_circuit circuit).

(* TODO(blaxill): the definitions should be equivalent *)
Lemma is_combinational_true_no_letrec {i o: Kind}:
  forall e: Kappa i o, NoLetRec e -> is_combinational e = true.
Abort.

