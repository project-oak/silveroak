(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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
Require Import Cava.Lib.VecConstEq.


Example ex1 : vecConstEq 8 42 (N2Bv_sized 8 42) = ret true.
Proof. trivial. Qed.

Example ex2 : vecConstEq 8 42 (N2Bv_sized 8 43) = ret false.
Proof. trivial. Qed.

Example ex3 : vecConstEq 1 1 (N2Bv_sized 1 1) = ret true.
Proof. trivial. Qed.

Example ex4 : vecConstEq 1 1 (N2Bv_sized 1 0) = ret false.
Proof. trivial. Qed.

Example ex5 : vecConstEq 1 3 (N2Bv_sized 1 1) = ret true.
Proof. trivial. Qed.

Definition vecConstEqInterface {n: nat}
  := combinationalInterface "vecConstEqInterface"
     [mkPort "v" (Vec Bit n)]
     [mkPort "o" Bit].

Definition vecConstEq8_42Netlist
  := makeNetlist vecConstEqInterface (vecConstEq 8 42).

Definition vecConstEq8_42_tb_inputs : list (Bvector 8) :=
  [N2Bv_sized 8 42; N2Bv_sized 8 254; N2Bv_sized 8 0].

Definition vecConstEq8_42_tb_expected_outputs : list bool
  := simulate (Comb (vecConstEq 8 42)) vecConstEq8_42_tb_inputs.

Definition vecConstEq8_42_tb
  := testBench "vecConstEq8_42_tb"
     vecConstEqInterface vecConstEq8_42_tb_inputs
     vecConstEq8_42_tb_expected_outputs.
