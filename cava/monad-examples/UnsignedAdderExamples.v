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

From Coq Require Import Ascii String.
From Coq Require Import Bool.Bool.
From Coq Require Import NArith.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Netlist.
Require Import Cava.Types.
Require Import Cava.BitArithmetic.
Require Import Cava.Monad.Cava.
Require Import Cava.Monad.UnsignedAdders.

(******************************************************************************)
(* Unsigned addition examples.                                                *)
(******************************************************************************)

Definition bv4_0  := nat_to_list_bits_sized 4  0.
Definition bv4_1  := nat_to_list_bits_sized 4  1.
Definition bv4_2  := nat_to_list_bits_sized 4  2.
Definition bv4_3  := nat_to_list_bits_sized 4  3.
Definition bv4_15 := nat_to_list_bits_sized 4 15.

Definition bv5_0  := nat_to_list_bits_sized 5  0.
Definition bv5_3  := nat_to_list_bits_sized 5  3.
Definition bv5_16 := nat_to_list_bits_sized 5 16.
Definition bv5_30 := nat_to_list_bits_sized 5 30.

(* Check 0 + 0 = 0 *)
Example add5_0_0 : combinational (unsignedAdd bv4_0 bv4_0) = bv5_0.
Proof. reflexivity. Qed.

(* Check 1 + 2 = 3 *)
Example add5_1_2 : combinational (unsignedAdd bv4_1 bv4_2) = bv5_3.
Proof. reflexivity. Qed.

(* Check 15 + 1 = 16 *)
Example add5_15_1 : combinational (unsignedAdd bv4_15 bv4_1) = bv5_16.
Proof. reflexivity. Qed.

(* Check 15 + 15 = 30 *)
Example add5_15_15 : combinational (unsignedAdd bv4_15 bv4_15) = bv5_30.
Proof. reflexivity. Qed.

(******************************************************************************)
(* Generate a 4-bit unsigned adder with 5-bit output.                         *)
(******************************************************************************)

Local Open Scope nat_scope.

Definition adder4Interface
  := mkCombinationalInterface "adder4"
     (Tuple2 (One ("a", BitVec [4])) (One ("b", BitVec [4])))
     (One ("sum", BitVec [5]))
     [].

Definition adder4Netlist
  := makeNetlist adder4Interface (fun '(a, b) => unsignedAdd a b).

Definition adder4_tb_inputs
  := [(bv4_0, bv4_0); (bv4_1, bv4_2); (bv4_15, bv4_1); (bv4_15, bv4_15)].

Definition adder4_tb_expected_outputs
  := map (fun '(a, b) => combinational (unsignedAdd a b)) adder4_tb_inputs.

Definition adder4_tb
  := testBench "adder4_tb" adder4Interface
     adder4_tb_inputs adder4_tb_expected_outputs.

(******************************************************************************)
(* Generate a three input 8-bit unsigned adder with 10-bit output.            *)
(******************************************************************************)

Definition adder8_3inputInterface
  := mkCombinationalInterface "adder8_3input"
     (Tuple2 (One ("a", BitVec [8])) (Tuple2 (One ("b", BitVec [8])) (One ("c", BitVec [8]))))
     (One ("sum", BitVec [10]))
     [].

Definition adder8_3inputNetlist
  := makeNetlist adder8_3inputInterface
     (fun '(a, (b, c)) => adder_3input a b c).

Local Open Scope N_scope.

Definition adder8_3input_tb_inputs :=
  map (fun '(x, (y, z)) => (nat_to_list_bits_sized 8 x,
                            (nat_to_list_bits_sized 8 y, nat_to_list_bits_sized 8 z)))
  [(17, (23, 95)); (4, (200, 30)); (255, (255, 200))].

Definition adder8_3input_tb_expected_outputs :=
  map (fun '(a, (b, c)) => combinational (adder_3input a b c)) adder8_3input_tb_inputs.

Definition adder8_3input_tb :=
  testBench "adder8_3input_tb" adder8_3inputInterface
  adder8_3input_tb_inputs adder8_3input_tb_expected_outputs.

