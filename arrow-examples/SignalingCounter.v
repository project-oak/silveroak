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

  Notation nibble := (Vector Bit 4).

  Definition counter :=
    <[fun "counter" is_valid value : nibble =>
      letrec counter =
        if is_valid
        then counter +% value
        else counter in
      counter
    ]>.
End notation.

Open Scope kind_scope.

Require Import Cava.Types.
Require Import Cava.Netlist.

Definition signaling_counter_Interface :=
   sequentialInterface "signaling_counter" "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "is_valid" Signal.Bit
     ;mkPort "value" (Signal.Vec Signal.Bit 4)]
     [mkPort "count" (Signal.Vec Signal.Bit 4)] [].

Definition signaling_counter_netlist :=
  build_netlist (closure_conversion counter) "signaling_counter" ("is_valid", "value") "count".

(* first for cycles have 'is_valid = false' and should not increment the counter *)
Definition signaling_counter_tb_inputs : list (bool * Bvector.Bvector 4) :=
  (repeat (false, N2Bv_sized 4 1) 4) ++ (repeat (true, N2Bv_sized 4 1) 4).

Definition signaling_counter_tb_expected_outputs : list (Bvector.Bvector 4) :=
  unroll_circuit_evaluation (closure_conversion counter) signaling_counter_tb_inputs.

Lemma arrow_and_expr_counter_semantics_agree:
  (map Bv2N signaling_counter_tb_expected_outputs) =
  (map Bv2N (interp_sequential ((counter : Kappa _ _) _) signaling_counter_tb_inputs)).
Proof. vm_compute; reflexivity. Qed.

Definition signaling_counter_tb :=
  testBench "signaling_counter_tb" signaling_counter_Interface
            signaling_counter_tb_inputs signaling_counter_tb_expected_outputs.

