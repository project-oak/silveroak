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

Require Import Coq.Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Section notation.
  Import KappaNotation.
  Local Open Scope category_scope.
  Local Open Scope kind_scope.

  Definition mux2_1
    : << Bit, << Bit, Bit >>, Unit >> ~> Bit :=
    <[ \ sel ab =>
      let '(a,b) = ab in
      let sel_a = and sel a in
      let inv_sel = not sel in
      let sel_b = and inv_sel b in
      let sel_out = or sel_a sel_b in
      sel_out
    ]>.
End notation.

Open Scope kind_scope.

Lemma mux2_1_is_combinational: is_combinational (closure_conversion mux2_1).
Proof. simply_combinational. Qed.

Require Import Cava.Types.
Require Import Cava.Netlist.
Require Import Cava.Signal.

Definition mux2_1_netlist :=
  build_netlist (closure_conversion mux2_1) "mux2_1" ("s", ("a", "b")) "o".

Definition mux2_1_tb_inputs : list (bool * (bool * bool)) :=
 [(false, (false, true));
  (false, (true, false));
  (false, (false, false));
  (true, (false, true));
  (true, (true, false));
  (true, (true, true))].

Definition mux2_1_tb_expected_outputs : list bool :=
 map (fun i => combinational_evaluation (closure_conversion mux2_1) i) mux2_1_tb_inputs.

Goal is_combinational (closure_conversion mux2_1). Proof. simply_combinational. Qed.

Definition mux2_1_tb :=
  testBench "mux2_1_tb"
   (combinationalInterface "mux2_1"
     [mkPort "s" Bit; mkPort "a" Bit; mkPort "b" Bit]
     [mkPort "o" Bit] [])
  (map (fun '(a,(b,c)) => (a,b,c)) mux2_1_tb_inputs) mux2_1_tb_expected_outputs.
