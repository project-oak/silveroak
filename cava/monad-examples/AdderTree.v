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

From Coq Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import NArith.
Require Import Omega.

From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
Import VectorNotations.

From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaMonad.
Require Import Cava.Monad.UnsignedAdders.

(******************************************************************************)
(* A generic description of all adder trees made from a syntheszable adder    *)
(* by using the tree combinator.                                              *)
(******************************************************************************)

Definition adderTree {m bit} `{Cava m bit} {sz: nat}
                     (n: nat) (v: Vector.t (Vector.t bit sz) (2^(n+1))) :
                     m (Vector.t bit sz) :=              
  tree n addNN v.

(******************************************************************************)
(* Some tests.                                                                *)
(******************************************************************************)

Definition v0 := N2Bv_sized 8  4.
Definition v2 := N2Bv_sized 8  6.
Definition v1 := N2Bv_sized 8 17.
Definition v3 := N2Bv_sized 8  3.

Local Open Scope N_scope.
Local Open Scope string_scope.

(* An adder tree with 2 inputs. *)

Local Open Scope nat_scope.

Definition adderTree2 {m bit} `{Cava m bit} {sz: nat}
                      (v : Vector.t (Vector.t bit sz) 2) : m (Vector.t bit sz)
  := adderTree 0 v.

Local Open Scope vector_scope.

Definition v0_v1 := [v0; v1].
Definition v0_plus_v1 : Bvector 8 := combinational (adderTree 0 v0_v1).

Example sum_vo_v1 : combinational (adderTree2 v0_v1) = N2Bv_sized 8 21.
Proof. reflexivity. Qed.

(* An adder tree with 4 inputs. *)

Definition adderTree4 {m bit} `{Cava m bit} {sz: nat}
                      (v : Vector.t (Vector.t bit sz) 4) : m (Vector.t bit sz)
  := adderTree 1 v.

Definition v0_3 := [v0; v1; v2; v3].
Definition sum_v0_3 : Bvector 8 := combinational (adderTree4 v0_3).

Example sum_v0_v1_v2_v3 : combinational (adderTree4 v0_3) = N2Bv_sized 8 30.
Proof. reflexivity. Qed.

Definition adder_tree_Interface name nrInputs bitSize
  := combinationalInterface name
     (mkPort "inputs" (BitVec (BitVec Bit bitSize) nrInputs))
     (mkPort "sum" (BitVec Bit bitSize))
     [].

(* Create netlist and test-bench for a 4-input adder tree. *)

Definition adder_tree4_8Interface := adder_tree_Interface "adder_tree4_8" 4 8.

Definition adder_tree4_8Netlist
  := makeNetlist adder_tree4_8Interface adderTree4.

Local Open Scope N_scope.

Definition adder_tree4_8_tb_inputs
  := map (fun i => Vector.map (N2Bv_sized 8) i)
     [[17;  42;  23;  95];
      [ 4;  13; 200;  30]; 
      [255; 74; 255; 200]
     ].

Definition adder_tree4_8_tb_expected_outputs
  := map (fun i => combinational (adderTree4 i)) adder_tree4_8_tb_inputs.

Definition adder_tree4_8_tb :=
  testBench "adder_tree4_8_tb" adder_tree4_8Interface
  adder_tree4_8_tb_inputs adder_tree4_8_tb_expected_outputs.

(* Create netlist for a 32-input adder tree. *)

Definition adder_tree32_8Interface
  := adder_tree_Interface "adder_tree32_8" 32 8.

Definition adder_tree32_8Netlist
  := makeNetlist adder_tree32_8Interface (adderTree 4).

(* Create netlist and test-bench for a 64-input adder tree. *)

Definition adder_tree64_8Interface
  := adder_tree_Interface "adder_tree64_8" 64 8.

Definition adder_tree64_8Netlist
  := makeNetlist adder_tree64_8Interface (adderTree 5).

Definition adder_tree64_8_tb_inputs
  := map (Vector.map (N2Bv_sized 8))
     (Vector.const 255 64 :: map (Vector.map N.of_nat)
     [vseq 0 64; vseq 64 64; vseq 128 64]).

Definition adder_tree64_8_tb_expected_outputs
  := map (fun i => combinational (adderTree 5 i)) adder_tree64_8_tb_inputs.

Definition adder_tree64_8_tb :=
  testBench "adder_tree64_8_tb" adder_tree64_8Interface
  adder_tree64_8_tb_inputs adder_tree64_8_tb_expected_outputs.

(* Create netlist and test-bench for a 64-input adder tree adding 128-bit words. *)

Definition adder_tree64_128Interface := adder_tree_Interface "adder_tree64_128" 64 128.

Definition adder_tree64_128Netlist
  := makeNetlist adder_tree64_128Interface (adderTree 5).

Definition adder_tree64_128_tb_inputs
  := map (Vector.map (N2Bv_sized 128))
     (Vector.const (2^128-1) 64 :: map (Vector.map N.of_nat)
     [vseq 0 64; vseq 64 64; vseq 128 64]).

Definition adder_tree64_128_tb_expected_outputs
  := map (fun i => combinational (adderTree 5 i)) adder_tree64_128_tb_inputs.

Definition adder_tree64_128_tb :=
  testBench "adder_tree64_128_tb" adder_tree64_128Interface
  adder_tree64_128_tb_inputs adder_tree64_128_tb_expected_outputs.
