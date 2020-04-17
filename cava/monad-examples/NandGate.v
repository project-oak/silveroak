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

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Netlist.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(* NAND gate example. Fist, let's define an overloaded NAND gate
   description. *)

Definition nand2Interface
  := mkCircuitInterface "nand2"
     (Tuple2 (One ("a", Bit)) (One ("b", Bit)))
     (One ("c", Bit))
     [].

Definition nand2_gate {m t} `{Cava m t} := and2 >=> inv.

Definition nand2Netlist := makeNetlist nand2Interface nand2.

(* A proof that the NAND gate implementation is correct. *)
Lemma nand2_behaviour : forall (a : bool) (b : bool),
                        combinational (nand2_gate (a, b)) = negb (a && b).
Proof.
  auto.
Qed.

(* A proof that the sequential NAND gate implementation is correct. *)
Lemma nand2_seq_behaviour : forall (a : list bool) (b : list bool),
                            sequential (nand2_gate (a, b)) = map (fun (i : bool * bool) => let (a, b) := i in
                                                             negb (a && b)) (combine a b).
Proof.
  intros.
  unfold sequential.
  unfold unIdent.
  simpl.
  rewrite map_map.
  rewrite map_ext_in_iff.
  intros.
  now destruct a0.  
Qed.

(* An exhuastive proof by analyzing all four cases. *)
Example nand_00 : combinational (nand2_gate (false, false)) = true.
Proof. reflexivity. Qed.

Example nand_01 : combinational (nand2_gate (false, true)) = true.
Proof. reflexivity. Qed.

Example nand_10 : combinational (nand2_gate (true, false)) = true.
Proof. reflexivity. Qed.

Example nand_11 : combinational (nand2_gate (true, true)) = false.
Proof. reflexivity. Qed.

(* Test bench tables for generated SystemVerilog simulation test bench *)
Definition nand_tb_inputs : list (bool * bool) :=
 [(false, false); (false, true); (true, false); (true, true)]. 

(* Compute expected outputs. *)
Definition nand_tb_expected_outputs : list bool :=
  map (fun i => combinational (nand2_gate i)) nand_tb_inputs.

Definition nand2_tb :=
  testBench "nand2_tb" nand2Interface nand_tb_inputs nand_tb_expected_outputs.

(******************************************************************************)
(* A nand-gate with registers after the AND gate and the INV gate.            *)
(******************************************************************************)

Definition pipelinedNAND {m t} `{Cava m t}
  := nand2_gate >=> delayBit >=> inv >=> delayBit.

Definition pipelinedNANDInterface
  := mkCircuitInterface "pipelinedNAND"
     (Tuple2 (One ("a", Bit)) (One ("b", Bit)))
     (One ("c", Bit))
     [].

Definition pipelinedNANDNetlist := makeNetlist pipelinedNANDInterface pipelinedNAND.

Definition pipelinedNAND_tb_inputs
  := [(false, false);
      (true, false);
      (false, true);
      (true, true);
      (false, false);
      (true, false);
      (true, false)].

Definition pipelinedNAND_tb_expected_outputs
  := [false; true; false; false; false; true; false].


Definition pipelinedNAND_tb
  := testBench "pipelinedNAND_tb" pipelinedNANDInterface
     pipelinedNAND_tb_inputs pipelinedNAND_tb_expected_outputs.

(******************************************************************************)
(* An contrived example of loopBit                                            *)
(******************************************************************************)

Definition loopedNAND {m bit} `{Cava m bit}
  := loopBit (second delayBit >=> nand2 >=> fork2).

Definition loopedNANDInterface
  := mkCircuitInterface "loopedNAND"
     (One ("a", Bit))
     (One ("b", Bit))
     [].

Definition loopedNANDNetlist := makeNetlist loopedNANDInterface loopedNAND.

Fixpoint loopedNAND_spec' (i : list bool) (state : bool) : list bool :=
  match i with
  | [] => []
  | x::xs => let newOutput := negb (x && state) in
             newOutput :: loopedNAND_spec' xs newOutput
  end.

Definition loopedNAND_tb_inputs :=
  [false; (* 10 *)
   false; (* 20 *)
   true;  (* 30 *)
   true;  (* 40 *)
   true;  (* 50 *)
   true;  (* 60 *)
   false; (* 70 *)
   false; (* 80 *)
   true;  (* 90 *)
   true;  (* 100 *)
   true;  (* 110 *)
   true   (* 120 *)
  ] .


Definition loopedNAND_tb_expected_outputs :=
  [true;  (* 10 *)
   true;  (* 20 *)
   false; (* 30 *)
   true;  (* 40 *)
   false; (* 50 *)
   true;  (* 60 *)
   true;  (* 70 *)
   true;  (* 80 *)
   false; (* 90 *)
   true;  (* 100 *)
   false; (* 110 *)
   true   (* 120 *)
  ].

Definition loopedNAND_tb
  := testBench "loopedNAND_tb" loopedNANDInterface
     loopedNAND_tb_inputs loopedNAND_tb_expected_outputs.

(*
                  10 a = 0, b = 1
                  20 a = 0, b = 1
                  30 a = 1, b = 0
                  40 a = 1, b = 1
                  50 a = 1, b = 0
                  60 a = 1, b = 1
                  70 a = 0, b = 1
                  80 a = 0, b = 1
                  90 a = 1, b = 1
                 100 a = 1, b = 0
                 110 a = 1, b = 1
                 120 a = 1, b = 0
*)
