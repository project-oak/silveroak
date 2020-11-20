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

From Cava Require Import Arrow.ArrowExport.

From Coq Require Import Strings.String Bool.Bvector Lists.List NArith.NArith
     Init.Nat micromega.Lia Arith.Plus.
Import ListNotations.
Import EqNotations.

Local Open Scope string_scope.

Section notation.
  Import KappaNotation.
  Local Open Scope category_scope.
  Local Open Scope kind_scope.

  Definition unsigned_adder a b c
  : << Vector Bit a, Vector Bit b, Unit >> ~> (Vector Bit c) :=
  <[ \ x y => unsigned_add a b c x y ]>.

  Definition adder3 s1 s2 s3
  : << Vector Bit s1, Vector Bit s2, Vector Bit s3, Unit >> ~> (Vector Bit _) :=
  <[ \ a b c => a + b + c ]>.

  Definition tree_adder a n
  : << Vector (Vector Bit a) (2^n), Unit >> ~> (Vector Bit a) :=
  <[ \ v => !(tree (Vector Bit a) n (unsigned_adder a a a)) v  ]>.

  Lemma max_nn_add_1_is_S_n: forall n, 1 + max n n = S n.
  Proof. intros; rewrite PeanoNat.Nat.max_id; auto. Qed.

  Definition growth_adder n
  : << Vector Bit n, Vector Bit n, Unit >> ~> Vector Bit (S n) :=
  <[ \ a b => typecast (a + b) ]>.

  Definition growth_tree_adder a n
  : << Vector (Vector Bit a) (2^n), Unit >> ~> Vector Bit (n + a) :=
  <[ \ v => !(dt_tree_fold' n a (Vector Bit) (growth_adder)) v  ]>.

  Definition adder445: << Vector Bit 4, Vector Bit 4, Unit >> ~> (Vector Bit 5)
    := unsigned_adder 4 4 5.

  Definition adder88810: << Vector Bit 8, Vector Bit 8, Vector Bit 8, Unit >> ~> (Vector Bit 10)
    := adder3 8 8 8.

  Definition adder444_tree_4: << Vector (Vector Bit 4) 4, Unit >> ~> (Vector Bit 4)
    := tree_adder 4 2.

  Definition adder444_tree_8: << Vector (Vector Bit 4) 8, Unit >> ~> (Vector Bit 4)
    := tree_adder 4 3.

  Definition adder444_tree_64: << Vector (Vector Bit 4) 64, Unit >> ~> (Vector Bit 4)
    := tree_adder 4 6.

  Definition growth_tree_8: << Vector (Vector Bit 4) 8, Unit >> ~> (Vector Bit 7)
    := growth_tree_adder 4 3.
End notation.

Lemma adder445_is_combinational: is_combinational (closure_conversion adder445).
Proof. simply_combinational. Qed.

Lemma adder88810_is_combinational: is_combinational (closure_conversion adder88810).
Proof. simply_combinational. Qed.

Require Import Cava.Types.
Require Import Cava.Netlist.

Definition adder445_interface
  := combinationalInterface "adder445"
     [mkPort "a" (Signal.Vec Signal.Bit 4); mkPort "b" (Signal.Vec Signal.Bit 4)]
     [mkPort "sum" (Signal.Vec Signal.Bit 5)]
     [].
Definition adder88810_interface
  := combinationalInterface "adder88810"
     [mkPort "a" (Signal.Vec Signal.Bit 8); mkPort "b" (Signal.Vec Signal.Bit 8); mkPort "c" (Signal.Vec Signal.Bit 8)]
     [mkPort "sum" (Signal.Vec Signal.Bit 10)]
     [].
Definition adder444_tree_4_interface
  := combinationalInterface "adder444_tree_4"
     [mkPort "vec" (Signal.Vec (Signal.Vec Signal.Bit 4) 4)]
     [mkPort "result" (Signal.Vec Signal.Bit 4)]
     [].
Definition adder444_tree_8_interface
  := combinationalInterface "adder444_tree_8"
     [mkPort "vec" (Signal.Vec (Signal.Vec Signal.Bit 4) 8)]
     [mkPort "result" (Signal.Vec Signal.Bit 4)]
     [].
Definition adder444_tree_64_interface
  := combinationalInterface "adder444_tree_64"
     [mkPort "vec" (Signal.Vec (Signal.Vec Signal.Bit 4) 64)]
     [mkPort "result" (Signal.Vec Signal.Bit 4)]
     [].
Definition growth_tree_8_interface
  := combinationalInterface "growth_tree_8"
     [mkPort "vec" (Signal.Vec (Signal.Vec Signal.Bit 4) 8)]
     [mkPort "result" (Signal.Vec Signal.Bit 7)]
     [].

Definition adder445_netlist :=
  build_netlist (closure_conversion adder445) "adder445" ("a","b") "sum".

Definition adder445_tb_inputs :=
  map (fun '(x, y) => (N2Bv_sized 4 x, N2Bv_sized 4 y))
  [(0, 0); (1, 2); (15, 1); (15, 15)]%N.

Definition adder445_tb_expected_outputs
  := map (fun i => combinational_evaluation (closure_conversion adder445) i) adder445_tb_inputs.

Definition adder445_tb
  := testBench "adder445_tb" adder445_interface
     adder445_tb_inputs adder445_tb_expected_outputs.

Definition adder88810_netlist :=
  build_netlist (closure_conversion adder88810) "adder88810" ("a",("b","c")) "sum".

Definition adder88810_tb_inputs :=
  map (fun '(x, y, z) => (N2Bv_sized 8 x, (N2Bv_sized 8 y, N2Bv_sized 8 z)))
  [(17, 23, 95); (4, 200, 30); (255, 255, 200)]%N.

Definition adder88810_tb_expected_outputs
  := map (fun i => combinational_evaluation (closure_conversion adder88810) i) adder88810_tb_inputs.

Definition adder88810_tb
  := testBench "adder88810_tb" adder88810_interface
     (map (fun '(a,(b,c)) => (a,b,c)) adder88810_tb_inputs) adder88810_tb_expected_outputs.

Definition adder444_tree_4_netlist :=
  build_netlist (closure_conversion adder444_tree_4) "adder444_tree_4" "vec" "result".

Definition adder444_tree_8_netlist :=
  build_netlist (closure_conversion adder444_tree_8) "adder444_tree_8" "vec" "result".

Definition adder444_tree_64_netlist :=
  build_netlist (closure_conversion adder444_tree_64) "adder444_tree_64" "vec" "result".

Definition adder444_tree_4_inputs :=
  map (fun '(x, y, z, w) => [N2Bv_sized 4 x; N2Bv_sized 4 y; N2Bv_sized 4 z; N2Bv_sized 4 w]%vector)
  [(0, 0, 0, 1); (1, 1, 1, 1); (1, 3, 5, 2); (15, 1, 1, 1)]%N.

Lemma adder444_tree_4_is_combinational: is_combinational (closure_conversion adder444_tree_4).
Proof. simply_combinational. Qed.

Definition adder444_tree_4_tb_expected_outputs
  := map (fun i => combinational_evaluation (closure_conversion adder444_tree_4) i) adder444_tree_4_inputs.

Definition adder444_tree_4_tb
  := testBench "adder444_tree_4_tb" adder444_tree_4_interface
     adder444_tree_4_inputs adder444_tree_4_tb_expected_outputs.

Definition growth_tree_8_netlist :=
  build_netlist (closure_conversion growth_tree_8) "growth_tree_8" "vec" "result".

Definition growth_tree_8_inputs :=
  map (Vector.map (N2Bv_sized 4))
  [[0; 0; 0; 0; 0; 0; 0; 1]%vector %N
  ;[1; 1; 1; 1; 1; 1; 1; 1]%vector %N
  ;[1; 2; 3; 4; 5; 6; 7; 8]%vector %N
  ;[15; 15; 15; 15; 15; 15; 15; 15]%vector %N
  ].

Lemma growth_tree_8_is_combinational: is_combinational (closure_conversion growth_tree_8).
Proof. simply_combinational. Qed.

Definition growth_tree_8_tb_expected_outputs
  := map (fun i => combinational_evaluation (closure_conversion growth_tree_8) i) growth_tree_8_inputs.

Definition growth_tree_8_tb
  := testBench "growth_tree_8_tb" growth_tree_8_interface
     growth_tree_8_inputs growth_tree_8_tb_expected_outputs.
