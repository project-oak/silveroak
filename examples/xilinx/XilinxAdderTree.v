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
Local Open Scope N_scope.
Local Open Scope vector_scope.

Section WithCava.
  Context {signal} `{Cava signal}.

  (****************************************************************************)
  (* A generic description of all adder trees made from a Xilinx adder        *)
  (* by using the tree combinator.                                            *)
  (****************************************************************************)
  Definition adderTree {sz: nat}
             (n: nat)
    : signal (Vec (Vec Bit sz) (2^n)) ->
      cava (signal (Vec Bit sz)) :=
    tree (fun '(x,y) => xilinxAdder x y).

  (****************************************************************************)
  (* An adder tree with 2 inputs.                                             *)
  (****************************************************************************)
  Definition adderTree2 {sz: nat}
                        (v : signal (Vec (Vec Bit sz) 2))
                        : cava (signal (Vec Bit sz))
    := adderTree 1 v.

  (******************************************************************************)
  (* An adder tree with 4 inputs.                                               *)
  (******************************************************************************)
  Definition adderTree4 {sz: nat}
                        (v : signal (Vec (Vec Bit sz) 4))
                        : cava (signal (Vec Bit sz))
    := adderTree 2 v.

End WithCava.

(******************************************************************************)
(* Some tests.                                                                *)
(******************************************************************************)

Definition v0 := N2Bv_sized 8  4.
Definition v1 := N2Bv_sized 8 17.
Definition v2 := N2Bv_sized 8  6.
Definition v3 := N2Bv_sized 8  3.

Definition v0_v1 : Vector.t (Bvector 8) 2 := [v0; v1].
Definition v0_plus_v1 : Bvector 8 := adderTree2 v0_v1.
Example sum_vo_v1 : v0_plus_v1 = N2Bv_sized 8 21.
Proof. reflexivity. Qed.

Definition v0_v1_v2_v3 := [v0; v1; v2; v3].
Example sum_v0_v1_v2_v3 :
  Bv2N (adderTree4 v0_v1_v2_v3) = 30.
Proof. reflexivity. Qed.

Definition adder_tree_Interface name nrInputs bitSize
  := combinationalInterface name
     [mkPort "inputs" (Vec (Vec Bit bitSize) nrInputs)]
     [mkPort "sum" (Vec Bit bitSize)].

(* Create netlist and test-bench for a 4-input adder tree. *)

Definition adder_tree4_8Interface := adder_tree_Interface "xadder_tree4_8" 4 8.

Definition adder_tree4_8Netlist
  := makeNetlist adder_tree4_8Interface adderTree4.

Definition adder_tree4_8_tb_inputs
  := map (fun i => Vector.map (N2Bv_sized 8) i)
     (Vector.const (2^8-1) 4 ::
     [[17; 42; 23; 95]; [4; 13; 200; 30]; [255; 74; 255; 200]; [44; 12; 92; 12];
      [9; 56; 2; 87];   [14; 72; 90; 11]; [64; 12; 92; 13];    [88; 24; 107; 200]]).

Definition adder_tree4_8_tb_expected_outputs
  := simulate (Comb adderTree4) adder_tree4_8_tb_inputs.

Definition adder_tree4_8_tb :=
  testBench "xadder_tree4_8_tb" adder_tree4_8Interface
  adder_tree4_8_tb_inputs adder_tree4_8_tb_expected_outputs.

(* Test to make sure this instance of the adder tree produces
   the expected output for the test bench case. *)
Example adder_tree_4_8_test:
   map Bv2N adder_tree4_8_tb_expected_outputs
   = [252; 177; 247; 16; 160; 154; 187; 181; 163]%list.
Proof. reflexivity. Qed.

(******************************************************************************)
(* Create netlist for a 32-input adder tree.                                  *)
(******************************************************************************)

Definition adder_tree32_8Interface := adder_tree_Interface "xadder_tree32_8" 32 8.

Definition adder_tree32_8Netlist
  := makeNetlist adder_tree32_8Interface (adderTree 5).

(* Create netlist and test-bench for a 64-input adder tree. *)

Definition adder_tree64_8Interface := adder_tree_Interface "xadder_tree64_8" 64 8.

Definition adder_tree64_8Netlist
  := makeNetlist adder_tree64_8Interface (adderTree 6).

Definition adder_tree64_8_tb_inputs
  := map (fun i => Vector.map (N2Bv_sized 8) (Vector.map N.of_nat i))
     [vseq 0 64; vseq 64 64; vseq 128 64].

Definition adder_tree64_8_tb_expected_outputs
  := simulate (Comb (adderTree 6)) adder_tree64_8_tb_inputs.

Definition adder_tree64_8_tb :=
  testBench "xadder_tree64_8_tb" adder_tree64_8Interface
  adder_tree64_8_tb_inputs adder_tree64_8_tb_expected_outputs.

(******************************************************************************)
(* Create netlist and test-bench for a 64-input adder of 128-bit inputs       *)
(******************************************************************************)

Definition adder_tree64_128Interface := adder_tree_Interface "xadder_tree64_128" 64 128.

Definition adder_tree64_128Netlist
  := makeNetlist adder_tree64_128Interface (adderTree 6).

Definition adder_tree64_128_tb_inputs
  := map (fun i => Vector.map (N2Bv_sized 128) i)
     (Vector.const (2^128-1) 64 :: map (Vector.map N.of_nat)
     [vseq 0 64; vseq 64 64; vseq 128 64]).

Definition adder_tree64_128_tb_expected_outputs
  := simulate (Comb (adderTree 6)) adder_tree64_128_tb_inputs.

Definition adder_tree64_128_tb :=
  testBench "xadder_tree64_128_tb" adder_tree64_128Interface
  adder_tree64_128_tb_inputs adder_tree64_128_tb_expected_outputs.

(******************************************************************************)
(* Create netlist and test-bench for a 128-input adder of 256-bit inputs      *)
(******************************************************************************)

Definition adder_tree128_256Interface := adder_tree_Interface "xadder_tree128_256" 128 256.

Definition adder_tree128_256Netlist
  := makeNetlist adder_tree128_256Interface (adderTree 7).

Definition adder_tree128_256_tb_inputs : list (Vector.t (Bvector 256) 128)
  := map (fun i => Vector.map (N2Bv_sized 256) i)
     (Vector.const (2^256-1) 128 :: map (Vector.map N.of_nat)
     [vseq 0 128; vseq 128 128; vseq 256 128]).

Definition adder_tree128_256_tb_expected_outputs
           : list (Bvector 256)
  := simulate (Comb (adderTree 7)) adder_tree128_256_tb_inputs.

Definition adder_tree128_256_tb :=
  testBench "xadder_tree128_256_tb" adder_tree128_256Interface
  adder_tree128_256_tb_inputs adder_tree128_256_tb_expected_outputs.
