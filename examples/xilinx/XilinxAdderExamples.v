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

Require Import Cava.Cava.

(****************************************************************************)
(* A few tests to check the unsigned adder.        *)
(****************************************************************************)

Definition v17  := N2Bv_sized 8 17.
Definition v52  := N2Bv_sized 8 52.
Definition v69  := N2Bv_sized 8 69.
Definition v70  := N2Bv_sized 8 70.
Definition v1   := N2Bv_sized 8 1.
Definition v255 := N2Bv_sized 8 255.
Definition v0   := N2Bv_sized 8 0.
Definition v200 := N2Bv_sized 8 200.
Definition v100 := N2Bv_sized 8 100.
Definition v44  := N2Bv_sized 8 44.

(* Perform a few basic checks to make sure the adder works. *)

Example xadd_17_52_0 : xilinxAdderWithCarry (v17, v52, false) =
                       (v69, false).
Proof. reflexivity. Qed.

Example xadd_17_52_1 : xilinxAdderWithCarry (v17, v52, true) =
                       (v70, false).
Proof. reflexivity. Qed.

Example xadd_1_255_1 : xilinxAdderWithCarry (v1, v255, false) =
                       (v0, true).
Proof. reflexivity. Qed.

Example xadd_0_255_1 : xilinxAdderWithCarry (v0, v255, true) =
                       (v0, true).
Proof. reflexivity. Qed.

Example xadd_200_100_0 : xilinxAdderWithCarry (v200, v100, false) =
                         (v44, true).
Proof. reflexivity. Qed.

(****************************************************************************)
(* A module definition for an 8-bit adder for SystemVerilog netlist         *)
(* generation.                                                              *)
(****************************************************************************)

Definition adder8Interface
  := combinationalInterface "adder8"
     [mkPort "a" (Vec Bit 8); mkPort "b" (Vec Bit 8); mkPort "cin" Bit]
     [mkPort "sum" (Vec Bit 8); mkPort "cout" Bit].

Definition adder8Netlist
  := makeNetlist adder8Interface xilinxAdderWithCarry.

Local Open Scope N_scope.

Definition adder8_tb_inputs :=
  map (fun '(a, b, cin)
       => (N2Bv_sized 8 a, N2Bv_sized 8 b, n2bool cin))
  [(7, 3, 0);
   (115, 67, 1);
   (92, 18, 0);
   (50, 200, 0);
   (255, 255, 0);
   (255, 255, 1)].

Definition adder8_tb_expected_outputs :=
  simulate (Comb xilinxAdderWithCarry) adder8_tb_inputs.

Definition adder8_tb :=
  testBench "adder8_tb" adder8Interface
  adder8_tb_inputs adder8_tb_expected_outputs.
