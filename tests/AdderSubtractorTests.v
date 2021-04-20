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
Require Import Cava.IP.AdderSubtractor.

Definition bv_0   := N2Bv_sized 8  0.
Definition bv_5   := N2Bv_sized 8  5.
Definition bv_7   := N2Bv_sized 8  7.
Definition bv_15  := N2Bv_sized 8 15.
Definition bv_255 := N2Bv_sized 8 255.

Example ex1 :
map Bv2N (simulate c_addsub_0 ((bv_5, bv_7) :: repeat (bv_0, bv_0) 7))
= [0%N; 0%N; 0%N; 0%N; 0%N; 0%N; 0%N; 12%N].
Proof. trivial. Qed.

Example ex2 :
map Bv2N (simulate c_addsub_0 ((bv_255, bv_255) :: repeat (bv_0, bv_0) 7))
= [0%N; 0%N; 0%N; 0%N; 0%N; 0%N; 0%N; 510%N].
Proof. trivial. Qed.

Definition adderInterface
  := sequentialInterface "c_addsub_0"
  (* is SSET the right reset port? *)
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "B" (Vec Bit 8); mkPort "A" (Vec Bit 8)]
     [mkPort "S" (Vec Bit 9)].

Definition adderNetlist := makeCircuitNetlist adderInterface c_addsub_0.

Definition adder_tb_inputs : list (Bvector 8 * Bvector 8) :=
  [(bv_0, bv_5);
   (bv_7, bv_0);
   (bv_5, bv_7);
   (bv_255, bv_5);
   (bv_7, bv_255);
   (bv_255, bv_255)]
  ++ repeat (bv_0, bv_0) 7.

Definition adder_tb_expected_outputs
  := simulate c_addsub_0 adder_tb_inputs.

Definition adder_tb
  := testBench "c_addsub_0_tb" adderInterface
     adder_tb_inputs adder_tb_expected_outputs.
