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

Require Import Cava.Tactics.
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

(* first four cycles have 'is_valid = false' and should not increment the counter *)
Definition signaling_counter_tb_inputs : list (bool * Bvector.Bvector 4) :=
  (repeat (false, N2Bv_sized 4 1) 4) ++ (repeat (true, N2Bv_sized 4 1) 4).

Definition signaling_counter_tb_expected_outputs : list (Bvector.Bvector 4) :=
  unroll_circuit_evaluation (closure_conversion counter) signaling_counter_tb_inputs.

Definition first_order_counter := to_skappa' (counter : Kappa _ _).
Goal wf_indexing [] first_order_counter.
Proof. cbn; tauto. Qed.

Lemma arrow_and_expr_counter_semantics_agree:
  (map Bv2N signaling_counter_tb_expected_outputs) =
  (map Bv2N (interp_sequential ((counter : Kappa _ _) _) signaling_counter_tb_inputs)).
Proof. vm_compute; reflexivity. Qed.

Lemma expr_single_step_counter_semantics_agree:
  (map Bv2N signaling_counter_tb_expected_outputs) =
  (map Bv2N (unroll_sequential_step first_order_counter signaling_counter_tb_inputs)).
Proof. vm_compute; reflexivity. Qed.

(* perhaps the structured state is actually not useful, as you then need to find
* it in the tupled structure ... *)
Definition proj_state_counter (state: skappa_state first_order_counter)
  : Bvector.Bvector 4
  := fst state.

Lemma state_increases_on_input s i s':
  i = (true, (N2Bv_sized _ 1, tt)) ->
  N.to_nat (Bv2N (proj_state_counter s)) < 15 ->
  (* exists o s', *)
  fst (sequential_step' first_order_counter s i) = s'
  ->
  S (N.to_nat (Bv2N (proj_state_counter s))) = N.to_nat (Bv2N (proj_state_counter s')).
Proof.
  intros.
  rewrite H in H1.
  rewrite <- H1.
  destruct s.
  Ltac reduce := cbn [
    unroll_sequential_step'
    sequential_step' sequential_step
    denote_apply_rightmost_tt
    first_order_counter fst snd
    sequential_step first_order_counter to_skappa' to_skappa counter module_body module_to_expr
    app index_env denote_kind primitive_output nth_error
    fst snd
    proj_state_counter
    ].
  reduce; repeat destruct_pair_let.
  cbn [proj_state_counter fst snd].

  (* next steps ?????
    context [(sequential_step
              match mux_item with
              ...]
    is equal to some gallina function effectively (+1)
    which should reduce to prove the goal
    *)
Admitted.

Definition signaling_counter_tb :=
  testBench "signaling_counter_tb" signaling_counter_Interface
            signaling_counter_tb_inputs signaling_counter_tb_expected_outputs.

