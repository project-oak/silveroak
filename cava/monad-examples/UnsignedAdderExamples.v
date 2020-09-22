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

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

From Coq Require Vector.
From Coq Require Import Bool.Bvector.

Require Import Omega.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaMonad.
Require Import Cava.Monad.UnsignedAdders.

(******************************************************************************)
(* Some handy test vectors                                                   *)
(******************************************************************************)

Definition bv4_0  := N2Bv_sized 4  0.
Definition bv4_1  := N2Bv_sized 4  1.
Definition bv4_2  := N2Bv_sized 4  2.
Definition bv4_3  := N2Bv_sized 4  3.
Definition bv4_15 := N2Bv_sized 4 15.

Definition bv5_0  := N2Bv_sized 5  0.
Definition bv5_3  := N2Bv_sized 5  3.
Definition bv5_16 := N2Bv_sized 5 16.
Definition bv5_30 := N2Bv_sized 5 30.

(******************************************************************************)
(* Test adders with no bit-growth and equal-sized inputs                      *)
(******************************************************************************)

(* Check 0 + 0 = 0 *)
Example add0_0 : combinational (addN bv4_0 bv4_0) = bv4_0.
Proof. reflexivity. Qed.

(* Check 15 + 1 = 0 *)
Example add15_1 : combinational (addN bv4_15 bv4_1) = bv4_0.
Proof. reflexivity. Qed.

(******************************************************************************)
(* Unsigned addition with growth examples.                                                *)
(******************************************************************************)

Definition adderGrowth {m bit} `{Cava m bit} {aSize bSize: nat}
                       (ab: Vector.t bit aSize * Vector.t bit bSize) :
                       m (Vector.t bit (1 + max aSize bSize)) :=
  let (a, b) := ab in
  unsignedAdd a b.

(* Check 0 + 0 = 0 *)
Example add5_0_0 : combinational (adderGrowth (bv4_0, bv4_0)) = bv5_0.
Proof. reflexivity. Qed.

(* Check 1 + 2 = 3 *)
Example add5_1_2 : combinational (adderGrowth (bv4_1, bv4_2)) = bv5_3.
Proof. reflexivity. Qed.

(* Check 15 + 1 = 16 *)
Example add5_15_1 : combinational (adderGrowth (bv4_15, bv4_1)) = bv5_16.
Proof. reflexivity. Qed.

(* Check 15 + 15 = 30 *)
Example add5_15_15 : combinational (adderGrowth (bv4_15, bv4_15)) = bv5_30.
Proof. reflexivity. Qed.

(******************************************************************************)
(* Generate a 4-bit unsigned adder with 5-bit output.                         *)
(******************************************************************************)

Local Open Scope nat_scope.

Definition adder4Interface
  := combinationalInterface "adder4"
     (mkPort "a" (BitVec Bit 4), mkPort "b" (BitVec Bit 4))
     (mkPort "sum" (BitVec Bit 5))
     [].

Definition adder4Netlist
  := makeNetlist adder4Interface adderGrowth.

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
  := combinationalInterface "adder8_3input"
     (mkPort "a" (BitVec Bit 8), mkPort "b" (BitVec Bit 8), mkPort "c" (BitVec Bit 8))
     (mkPort "sum" (BitVec Bit 10))
     [].

Definition add3InputTuple {m bit} `{Cava m bit}
                          (aSize bSize cSize: nat)
                          (abc: Vector.t bit aSize *
                                Vector.t bit bSize *
                                Vector.t bit cSize) :
                          m (Vector.t bit (1 + max (1 + max aSize bSize) cSize)) :=
  let '(a, b, c) := abc in adder_3input a b c.

Definition adder8_3inputNetlist
  := makeNetlist adder8_3inputInterface (add3InputTuple 8 8 8).

Local Open Scope N_scope.

Definition adder8_3input_tb_inputs :=
  map (fun '(x, y, z) => (N2Bv_sized 8 x, N2Bv_sized 8 y, N2Bv_sized 8 z))
  [(17, 23, 95); (4, 200, 30); (255, 255, 200)].

Definition adder8_3input_tb_expected_outputs :=
  map (fun i => combinational (add3InputTuple 8 8 8 i)) adder8_3input_tb_inputs.

Definition adder8_3input_tb :=
  testBench "adder8_3input_tb" adder8_3inputInterface
  adder8_3input_tb_inputs adder8_3input_tb_expected_outputs.
