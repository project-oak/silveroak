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

Definition bv2_0  := N2Bv_sized 2  0.
Definition bv2_3  := N2Bv_sized 2  3.
Definition bv3_0  := N2Bv_sized 3  0.
Definition bv3_5  := N2Bv_sized 3  5.
Definition bv3_7  := N2Bv_sized 3  7.
Definition bv5_15 := N2Bv_sized 5 15.

(* Check 3 * 5 = 30 *)
Example mult3_5 : combinational (unsignedMult bv2_3 bv3_5) = bv5_15.
Proof. reflexivity. Qed.

(* A top-level multiplier circuit that can be compiled to a top-level
   SystemVerilog circuit. *)
Definition multiplier {m bit} `{Cava m bit} {aSize bSize: nat}
                      (ab: Vector.t bit aSize * Vector.t bit bSize) :
                      m (Vector.t bit (aSize + bSize)) :=
  let (a, b) := ab in
  unsignedMult a b.

(* Check 3 * 5 = 30 *)
Example mult3_5_top : combinational (multiplier (bv2_3, bv3_5)) = bv5_15.
Proof. reflexivity. Qed.

(******************************************************************************)
(* Generate an unsigned multiplier with 2 and 3 bit inputs and 5-bit result.  *)
(******************************************************************************)

Local Open Scope nat_scope.

Definition mult2_3_5Interface
  := combinationalInterface "mult2_3_5"
     (mkPort "a" (Vec Bit 2), mkPort "b" (Vec Bit 3))
     (mkPort "product" (Vec Bit 5))
     [].

Definition mult2_3_5Netlist
  := makeNetlist mult2_3_5Interface multiplier.

Definition mult2_3_5_tb_inputs
  := [(bv2_3, bv3_5); (bv2_3, bv3_7); (bv2_0, bv3_0)].

Definition mult2_3_5_tb_expected_outputs
  := map (fun ab => combinational (multiplier ab)) mult2_3_5_tb_inputs.

Definition  mult2_3_5_tb
  := testBench "mult2_3_5_tb" mult2_3_5Interface
     mult2_3_5_tb_inputs mult2_3_5_tb_expected_outputs.

