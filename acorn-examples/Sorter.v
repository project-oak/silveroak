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

Require Import ExtLib.Structures.Monads.

Require Import Coq.Strings.Ascii Coq.Strings.String.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bvector.
Import VectorNotations.

Require Import Coq.Arith.PeanoNat Coq.NArith.NArith.
Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.Multiplexers.
Existing Instance CavaCombinationalNet.

Require Import Coq.micromega.Lia.

Local Open Scope vector_scope.

Section WithCava.
  Context {signal} `{Cava signal}.

  Definition twoSorter {signal} `{Cava signal} {n}
                     (ab:  signal (Vec (Vec Bit n) 2)) :
                     cava (signal (Vec (Vec Bit n) 2)) :=
   a <- indexConst ab 0 ;;
   b <- indexConst ab 1 ;;
   comparison <- greaterThanOrEqual (a, b) ;;
   negComparison <- inv comparison ;;
   out0 <- mux2 comparison (a, b) ;;
   out1 <- mux2 negComparison (a, b) ;;
   unpeel [out0; out1].

End WithCava.

Definition two_sorter_Interface bitSize
  := combinationalInterface "two_sorter"
     [mkPort "inputs" (Vec (Vec Bit bitSize) 2)]
     [mkPort "sorted" (Vec (Vec Bit bitSize) 2)]
     [].

Definition two_sorter_Netlist
  := makeNetlist (two_sorter_Interface 8) twoSorter.

Definition v0 := N2Bv_sized 8   5.
Definition v1 := N2Bv_sized 8 157.
Definition v2 := N2Bv_sized 8 255.
Definition v3 := N2Bv_sized 8  63.

Definition two_sorter_tb_inputs : list (Vector.t (Bvector 8) _) :=
  [[v0; v1];
   [v1; v0];
   [v1; v2];
   [v2; v1];
   [v2; v3];
   [v3; v2]
  ].

Definition adder_tree4_8_tb_expected_outputs : list (Vector.t (Bvector 8) _) :=
  multistep (Comb twoSorter) two_sorter_tb_inputs.

Definition two_sorter_tb :=
  testBench "two_sorter_tb" (two_sorter_Interface 8)
  two_sorter_tb_inputs adder_tree4_8_tb_expected_outputs.

Definition twoSorterSpec {bw: nat} (ab : Vector.t (Bvector bw) 2) :
                                   Vector.t (Bvector bw) 2 :=
  let a := @Vector.nth_order _ 2 ab 0 (ltac:(lia)) in
  let b := @Vector.nth_order _ 2 ab 1 (ltac:(lia)) in
  if (Bv2N b <=? Bv2N a)%N then
    [b; a]
  else
    [a; b].

Lemma twoSorterCorrect {bw : nat} (v : Vector.t (Bvector bw) 2) :
  unIdent (@twoSorter combType _ _ v) = twoSorterSpec v.
Proof.
  constant_vector_simpl v.
  cbv [twoSorterSpec nth_order].
  simpl.
  destruct (Bv2N _ <=? Bv2N _)%N; reflexivity.
Qed.
