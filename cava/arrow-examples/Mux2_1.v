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

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Instances.Combinational.

Require Import Coq.Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Local Open Scope string_scope.

Section definition.
  Import KappaNotation.

  Variable var: Kind -> Kind -> Type.

  Definition mux2_1
  : kappa_sugared var << Bit, << Bit, Bit >>, Unit >> Bit :=
  <[ \ sel ab =>
    let '(a,b) = ab in
    let sel_a = and sel a in
    let inv_sel = not sel in
    let sel_b = and inv_sel b in
    let sel_out = or sel_a sel_b in
    sel_out
  ]>.
End definition.

Definition mux2_1_structure := to_constructive (Desugar mux2_1) (ltac:(auto_kappa_wf)).

Lemma mux2_1_is_combinational: wf_combinational (toCava mux2_1_structure _).
Proof. combinational_obvious. Qed.

Require Import Cava.Arrow.Instances.Netlist.
Require Import Cava.Types.
Require Import Cava.Netlist.

Definition mux2_1_Interface :=
   combinationalInterface "mux2_1"
     (mkPort "s" Bit, (mkPort "a" Bit, mkPort "b" Bit))
     (mkPort "o" Bit)
     [].

Definition mux2_1_netlist :=
  makeNetlist mux2_1_Interface 
    (toCava mux2_1_structure NetlistCava).

Definition mux2_1_tb_inputs : list (bool * (bool * bool)) := 
 [(false, (false, true));
  (false, (true, false));
  (false, (false, false));
  (true, (false, true));
  (true, (true, false));
  (true, (true, true))].

(* Using `evaluate_to_terms` for a nicer extracted value *)
Definition mux2_1_tb_expected_outputs : list bool.
Proof. evaluate_to_terms mux2_1_structure mux2_1_is_combinational mux2_1_tb_inputs. Defined.

Definition mux2_1_tb :=
  testBench "mux2_1_tb" mux2_1_Interface
            mux2_1_tb_inputs mux2_1_tb_expected_outputs.