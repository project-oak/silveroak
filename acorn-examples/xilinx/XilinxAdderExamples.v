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

Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.XilinxAdder.

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

Example xadd_17_52_0 : combinational (xilinxAdderWithCarry ([false], ([v17], [v52]))) =
                                     ([v69], [false]).
Proof. reflexivity. Qed.

Example xadd_17_52_1 : combinational (xilinxAdderWithCarry ([true], ([v17], [v52]))) =
                                     ([v70], [false]).
Proof. reflexivity. Qed.

Example xadd_1_255_1 : combinational (xilinxAdderWithCarry ([false], ([v1], [v255]))) =
                                     ([v0], [true]).
Proof. reflexivity. Qed.

Example xadd_0_255_1 : combinational (xilinxAdderWithCarry ([true], ([v0], [v255]))) =
                                     ([v0], [true]).
Proof. reflexivity. Qed.

Example xadd_200_100_0 : combinational (xilinxAdderWithCarry ([false], ([v200], [v100]))) =
                                       ([v44], [true]).
Proof. reflexivity. Qed.

(****************************************************************************)
(* A module definition for an 8-bit adder for SystemVerilog netlist         *)
(* generation.                                                              *)
(****************************************************************************)

Definition adder8Interface
  := combinationalInterface "adder8"
     [mkPort "cin" Bit; mkPort "a" (Vec Bit 8); mkPort "b" (Vec Bit 8)]
     [mkPort "sum" (Vec Bit 8); mkPort "cout" Bit]
     [].

(* Produce a version of the xilinxAdderWithCarry with a flat-tuple input. *)
Definition xilinxAdderWithCarryFlat {signal} `{Cava signal} {n}
                                    '(cin, a, b)
                                    : cava (signal (Vec Bit n) * signal Bit) :=
  xilinxAdderWithCarry (cin, (a, b)).

Definition adder8Netlist
  := makeNetlist adder8Interface xilinxAdderWithCarryFlat.

Local Open Scope N_scope.

Definition adder8_tb_inputs :=
  map (fun '(cin, (a, b))
       => (n2bool cin, N2Bv_sized 8 a, N2Bv_sized 8 b))
  [(0, (7, 3));
   (1, (115, 67));
   (0, (92, 18));
   (0, (50, 200));
   (0, (255, 255));
   (1, (255, 255))].

Definition adder8_tb_expected_outputs :=
  map (fun '(i0,i1,i2) =>
         let '(r1,r2) := combinational (xilinxAdderWithCarryFlat ([i0],[i1],[i2])%list) in
         (List.hd (defaultCombValue _) r1, List.hd (defaultCombValue _) r2))
      adder8_tb_inputs.

Definition adder8_tb :=
  testBench "adder8_tb" adder8Interface
  adder8_tb_inputs adder8_tb_expected_outputs.
