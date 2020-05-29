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
Import ListNotations.

From Coq Require Arith.PeanoNat.
Require Import Omega.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Monad.Cava.
Require Import Cava.Netlist.
Require Import Cava.Types.
Require Import Cava.BitArithmetic.
Require Import Cava.Signal.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Definition mux2_1 {m bit} `{Cava m bit} '(sel, (a, b)) : m bit :=
  o <- indexBitArray [a; b] [sel] ;;
  ret o.

Example m1: combinational (mux2_1 (false, (false, true))) = false.
Proof. reflexivity. Qed.

Example m2: combinational (mux2_1 (false, (true, false))) = true.
Proof. reflexivity. Qed.

Example m3: combinational (mux2_1 (true, (false, true))) = true.
Proof. reflexivity. Qed.

Example m4: combinational (mux2_1 (true, (true, false))) = false.
Proof. reflexivity. Qed.

Definition mux2_1_Interface
  := mkCircuitInterface "mux2_1"
     (Tuple2 (One ("sel", Bit)) (Tuple2 (One ("i0", Bit)) (One ("i1", Bit))))
     (One ("o", Bit))
     [].

Definition mux2_1Netlist := makeNetlist mux2_1_Interface mux2_1.

Definition mux2_1_tb_inputs :=
  [(false, (false, true));
   (false, (true, false));
   (true, (false, true));
    (true, (true, false))].

Definition mux2_1_tb_xpected_outputs
  := map (fun i => combinational (mux2_1 i)) mux2_1_tb_inputs.

Definition mux2_1_tb
  := testBench "mux2_1_tb" mux2_1_Interface
     mux2_1_tb_inputs mux2_1_tb_xpected_outputs.

Definition muxBus {m bit} `{Cava m bit} '(sel, i) : m (list bit) :=
  o <- indexArray i sel ;;
  ret o.

Definition v0 := nat_to_list_bits_sized 8   5.
Definition v1 := nat_to_list_bits_sized 8 157.
Definition v2 := nat_to_list_bits_sized 8 255.
Definition v3 := nat_to_list_bits_sized 8  63.
Definition v := [v0; v1; v2; v3].

Example m5: combinational (muxBus ([false; false], v)) = v0.
Proof. reflexivity. Qed.

Example m6: combinational (muxBus ([true; false], v)) = v1.
Proof. reflexivity. Qed.

Example m7: combinational (muxBus ([false; true], v)) = v2.
Proof. reflexivity. Qed.

Example m8: combinational (muxBus ([true; true], v)) = v3.
Proof. reflexivity. Qed.

Definition muxBus4_8Interface
  := mkCircuitInterface "muxBus4_8"
     (Tuple2 (One ("sel", BitVec [2])) (One ("i", BitVec [4; 8])))
     (One ("o", BitVec [8]))
     [].

Definition muxBus4_8Netlist := makeNetlist muxBus4_8Interface muxBus.

Definition muxBus4_8_tb_inputs :=
  [([false; false], v);
   ([true;  false], v);
   ([false; true],  v);
   ([true; true],   v)
  ].

Definition muxBus4_8_tb_expected_outputs
  := map (fun i => combinational (muxBus i)) muxBus4_8_tb_inputs.

Definition muxBus4_8_tb
  := testBench "muxBus4_8_tb" muxBus4_8Interface
     muxBus4_8_tb_inputs muxBus4_8_tb_expected_outputs.
