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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.BitArithmetic.
Require Import Cava.Netlist.
Require Import Cava.Types.
Require Import Cava.Monad.XilinxAdder.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(****************************************************************************)
(* A few tests to check the unsigned adder.        *)
(****************************************************************************)


Definition v0   := [0;0;0;0;0;0;0;0].
Definition v1   := [1;0;0;0;0;0;0;0].
Definition v2   := [0;1;0;0;0;0;0;0].
Definition v3   := [1;1;1;1;1;1;1;1].
Definition v4   := [1;0;0;0;0;0;0;0].
Definition v5   := [1;1;1;1;1;1;1;1].
Definition v6   := [1;1;1;1;1;1;1;1].
Definition v255 := [1;1;1;1;1;1;1;1].

Definition eval_xilinxAdder cin a b :=
  let '(sum, carry)
    := combinational
       (xilinxAdderWithCarry (nat2bool cin, (toVec a, toVec b))) in
  (fromVec sum, Nat.b2n carry).

(* Perform a few basic checks to make sure the adder works. *)

Example v1_plus_v2 : eval_xilinxAdder 0 v1 v2 = ([1; 1; 0; 0; 0; 0; 0; 0], 0).
Proof. reflexivity. Qed.

Example v0_plus_v1 : eval_xilinxAdder 0 v0 v1 = ([1; 0; 0; 0; 0; 0; 0; 0], 0).
Proof. reflexivity. Qed.

Example v255_plus_v1 : eval_xilinxAdder 0 v255 v1 = ([0; 0; 0; 0; 0; 0; 0; 0], 1).
Proof. reflexivity. Qed.

Example v255_plus_v0_cin1 : eval_xilinxAdder 1 v255 v0 = ([0; 0; 0; 0; 0; 0; 0; 0], 1).
Proof. reflexivity. Qed.

Example v255_plus_255_cin1 : eval_xilinxAdder 1 v255 v255 = ([1; 1; 1; 1; 1; 1; 1; 1], 1).
Proof. reflexivity. Qed.

Example v3_plus_v4 : eval_xilinxAdder 0 v3 v4 = ([0; 0; 0; 0; 0; 0; 0; 0], 1).
Proof. reflexivity. Qed.

Example v5_plus_v6 : eval_xilinxAdder 0 v5 v6 = ([0; 1; 1; 1; 1; 1; 1; 1], 1).
Proof. reflexivity. Qed.

(****************************************************************************)
(* A module definition for an 8-bit adder for SystemVerilog netlist         *)
(* generation.                                                              *)
(****************************************************************************)

Definition adder8Interface
  := mkCircuitInterface "adder8"
     (Tuple2 (One ("cin", Bit)) (Tuple2 (One ("a", BitVec [8])) (One ("b", BitVec [8]))))
     (Tuple2 (One ("sum", BitVec [8])) (One ("cout", Bit)))
     [].

Definition adder8Netlist := makeNetlist adder8Interface xilinxAdderWithCarry.

Local Open Scope N_scope.

Definition adder8_tb_inputs :=
  map (fun '(cin, (a, b))
       => (n2bool cin, (nat_to_list_bits_sized 8 a, nat_to_list_bits_sized 8 b)))
  [(0, (7, 3));
   (1, (115, 67));
   (0, (92, 18));
   (0, (50, 200));
   (0, (255, 255));
   (1, (255, 255))].

Definition adder8_tb_expected_outputs :=
  map (fun i => combinational (xilinxAdderWithCarry i)) adder8_tb_inputs.

Definition adder8_tb :=
  testBench "adder8_tb" adder8Interface
  adder8_tb_inputs adder8_tb_expected_outputs.

