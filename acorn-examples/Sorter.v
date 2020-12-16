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

Require Import Coq.micromega.Lia.

Local Open Scope vector_scope.

Section WithCava.
  Context {signal} `{Cava signal} `{Monad cava}.

Definition twoSorter {signal} `{Cava signal} `{Monad cava} {n}
                     (ab:  signal (Vec (Vec Bit n) 2)) :
                     cava (signal (Vec (Vec Bit n) 2)) :=
   let a := indexConst ab 0 in
   let b := indexConst ab 1 in
   comparison <- greaterThanOrEqual a b ;;
   negComparison <- inv comparison ;;
   let sorted : Vector.t (signal (Vec Bit n)) 2 :=
     [indexAt ab (unpeel [comparison]);
      indexAt ab (unpeel [negComparison])] in
   ret (unpeel sorted).

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
  map (fun i => combinational (twoSorter i)) two_sorter_tb_inputs.

Definition two_sorter_tb :=
  testBench "two_sorter_tb" (two_sorter_Interface 8)
  two_sorter_tb_inputs adder_tree4_8_tb_expected_outputs.

Definition twoSorterSpec {bw: nat} (ab : Vector.t (Bvector bw) 2) :
                                   Vector.t (Bvector bw) 2 :=
  let a := @Vector.nth_order _ 2 ab 0 (ltac:(lia)) in
  let b := @Vector.nth_order _ 2 ab 1 (ltac:(lia)) in
  if N.to_nat (Bv2N b) <=? N.to_nat (Bv2N a) then
    [b; a]
  else
    [a; b].
