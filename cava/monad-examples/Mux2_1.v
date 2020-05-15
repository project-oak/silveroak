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

Require Import ExtLib.Structures.Monads.

Require Import Cava.Monad.Cava.
Require Import Cava.Netlist.

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