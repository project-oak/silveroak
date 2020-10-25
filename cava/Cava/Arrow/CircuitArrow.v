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

From Coq Require Import Lists.List NaryFunctions String Arith NArith Vector Lia.

Import ListNotations.
Import VectorNotations.

From Cava Require Import Arrow.Classes.Category Arrow.Classes.Arrow.
From Cava Require Import Arrow.ArrowKind.
From Cava Require Import Arrow.Primitives.

Local Open Scope category_scope.
Local Open Scope arrow_scope.

Class CircuitArrow := {
  circuit_cat :> Category Kind;
  circuit_arr :> Arrow Kind circuit_cat Unit Tuple;
  circuit_rew :> Arrows.RewriteOrDefault circuit_arr;
  circuit_ann :> Arrows.Annotation circuit_arr string;
  circuit_imp :> Arrows.Impossible circuit_arr;
  circuit_prim :> Arrows.Primitive circuit_arr
    Primitives.CircuitPrimitive Primitives.primitive_input Primitives.primitive_output;
  circuit_drop :> Arrows.Drop circuit_arr;
  circuit_copy :> Arrows.Copy circuit_arr;
  circuit_swap :> Arrows.Swap circuit_arr;
  circuit_loop :> Arrows.Loop circuit_arr;
}.

Coercion circuit_cat : CircuitArrow >-> Category.
Coercion circuit_arr : CircuitArrow >-> Arrow.
Coercion circuit_rew : CircuitArrow >-> Arrows.RewriteOrDefault.
Coercion circuit_ann : CircuitArrow >-> Arrows.Annotation.
Coercion circuit_imp : CircuitArrow >-> Arrows.Impossible.
Coercion circuit_prim : CircuitArrow >-> Arrows.Primitive.
Coercion circuit_drop : CircuitArrow >-> Arrows.Drop.
Coercion circuit_copy : CircuitArrow >-> Arrows.Copy.
Coercion circuit_swap : CircuitArrow >-> Arrows.Swap.
Coercion circuit_loop : CircuitArrow >-> Arrows.Loop.

