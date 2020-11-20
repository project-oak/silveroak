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


From Cava Require Import Arrow.ArrowExport.
From Coq Require Import Lists.List NArith.NArith Strings.String.
Import ListNotations.

Local Open Scope string_scope.

Section notation.
  Import KappaNotation.
  Local Open Scope category_scope.
  Local Open Scope kind_scope.

  Definition counter n
    : << Unit >> ~> Vector Bit n :=
    <[
      letrec counter = counter +% #1 in
      counter
    ]>.
End notation.

Open Scope kind_scope.

Require Import Cava.Types.
Require Import Cava.Netlist.

Definition counter_3_Interface :=
   sequentialInterface "counter_3" "clk" PositiveEdge "rst" PositiveEdge
     [] [mkPort "count" (Signal.Vec Signal.Bit 3)] [].

Definition counter_3_netlist :=
  build_netlist (closure_conversion (counter 3)) "counter_3_netlist" tt "count".

Definition counter_3_tb_inputs : list unit :=
 repeat tt 8.

Definition counter_3_tb_expected_outputs : list (Bvector.Bvector 3) :=
  unroll_circuit_evaluation (closure_conversion (counter 3)) (repeat tt 8).

Definition counter_3_tb :=
  testBench "counter_3_tb" counter_3_Interface
            counter_3_tb_inputs counter_3_tb_expected_outputs.

