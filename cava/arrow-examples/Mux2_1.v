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

From Arrow Require Import Category.
From Cava Require Import Arrow.ArrowExport Arrow.CavaArrow.

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

Definition mux2_1_Interface :=
   combinationalInterface "mux2_1"
     (mkPort "s" Kind.Bit, (mkPort "a" Kind.Bit, mkPort "b" Kind.Bit))
     (mkPort "o" Kind.Bit)
     [].

Definition mux2_1_netlist :=
  makeNetlist mux2_1_Interface (build_netlist (closure_conversion mux2_1)).

Definition mux2_1_tb_inputs : list (bool * (bool * bool)) := 
 [(false, (false, true));
  (false, (true, false));
  (false, (false, false));
  (true, (false, true));
  (true, (true, false));
  (true, (true, true))].

(* Using `evaluate_to_terms` for a nicer extracted value *)
Definition mux2_1_tb_expected_outputs : list bool :=

 map (fun i => combinational_evaluation (closure_conversion mux2_1) mux2_1_is_combinational i) mux2_1_tb_inputs.

Goal forall x, interp_combinational (mux2_1 _) x = false.
Proof. intros.
  cbv [mux2_1].
  time simpl. (* 0.02 s *)
  (* 
    (let
  '(x0, y) := x in
    let
    '(x1, _) := y in
    (x0 && (let '(x2, _) := x1 in x2) || negb x0 && (let '(_, y0) := x1 in y0))%bool) =
  false *)
Abort.

Goal 
  forall x, combinational_evaluation' (closure_conversion mux2_1) x = false.
Proof. intros.
  cbv [mux2_1].
  cbv [closure_conversion].
  cbv [closure_conversion'].
  Set Printing Implicit.
  time cbv [Arrow.first Arrow.arrow_category Arrow.product CircuitArrow].
  Show.




  Opaque asdfasfdcompose.

  cbv [Arrow.first Arrow.arrow_category Arrow.product CircuitArrow ].
  Set Ltac Profiling.
  Time  apply f_equal.




  time simpl. (* 2.88 s *)
  Show Ltac Profile.
    (* snd (let '(x0, y) := x in (y, x0)) &&
  (let
    '(x0, _) :=
    snd (let '(x0, y) := fst (let '(x0, y) := x in (y, x0)) in (y, x0)) in x0)
  || negb (snd (let '(x0, y) := x in (y, x0))) &&
      (let
      '(_, y) :=
        snd (let '(x0, y) := fst (let '(x0, y) := x in (y, x0)) in (y, x0)) in
        y))%bool = false *)

  (* cbv [Arrow.first Arrow.arrow_category Arrow.product CircuitArrow ].
  cbv [Arrow.swap Arrow.arrow_category Arrow.product CircuitArrow CircuitArrowSwap].
  cbv [Arrow.uncancelr Arrow.arrow_category Arrow.product CircuitArrow CircuitArrowSwap]. *)


Definition mux2_1_tb :=
  testBench "mux2_1_tb" mux2_1_Interface
            mux2_1_tb_inputs mux2_1_tb_expected_outputs.