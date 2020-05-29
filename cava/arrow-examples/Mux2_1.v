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
Require Import Cava.Arrow.Instances.Netlist.

Require Import Cava.Types.
Require Import Cava.Netlist.

Require Import Coq.Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Definition mux2_1'
: Kappa (bit ** (bit ** bit) ** unit) bit :=
<[ \ sel ab =>
   let a = fst' ab in
   let b = snd' ab in
   let sel_a = !and_gate sel a in
   let inv_sel = !not_gate sel in
   let sel_b = !and_gate inv_sel b in
   let sel_out = !or_gate sel_a sel_b in
   sel_out
]>.
Definition mux2_1 Cava := toCava Cava (Closure_conversion mux2_1').
 
Local Open Scope string_scope.

Definition mux2_1_Interface :=
   mkCircuitInterface "mux2_1"
     (Tuple2 (One ("s", Bit)) (Tuple2 (One ("a", Bit)) (One ("b", Bit))))
     (One ("o", Bit))
     [].

Definition mux2_1_netlist :=
  makeNetlist mux2_1_Interface
    (contraRemoveTerminal (mux2_1 NetlistCava)).

Definition mux2_1_tb_inputs : list (bool * (bool * bool)) :=
 [(false, (false, true));
  (false, (true, false));
  (false, (false, false));
  (true, (false, true));
  (true, (true, false));
  (true, (true, true))].

Definition mux2_1_tb_expected_outputs : list bool :=
  map (fun '(s, (a,b)) => (@mux2_1 Combinational) (s, ((a, b), tt)))
      mux2_1_tb_inputs.       

Definition mux2_1_tb :=
  testBench "mux2_1_tb" mux2_1_Interface
            mux2_1_tb_inputs mux2_1_tb_expected_outputs.