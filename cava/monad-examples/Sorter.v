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

From Coq Require Import Ascii String.

From Coq Require Import Lists.List.
Import ListNotations.

From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
Import VectorNotations.

From Coq Require Import NArith.Ndigits.

Require Import Cava.Cava.
Require Import Cava.VectorUtils.
Require Import Cava.Monad.CavaMonad.

From Coq Require Import Lia Omega.

Local Open Scope vector_scope.

Lemma zero_lt_z: 0 < 2. auto. Qed.
Lemma one_lt_z: 1 < 2. auto. Qed.

Definition twoSorter {m bit} `{Cava m bit} {n}
                     (ab: Vector.t (smashTy bit (BitVec Bit n)) 2) :
                     m (Vector.t (Vector.t bit n) 2) :=
   let a := @Vector.nth_order _ 2 ab 0 zero_lt_z in
   let b := @Vector.nth_order _ 2 ab 1 one_lt_z in
   comparison <- greaterThanOrEqual a b ;;
   negComparison <- inv comparison ;;
   let sorted : Vector.t (Vector.t bit n) 2 := [indexAt ab [comparison];
                                                indexAt ab [negComparison]] in
   ret sorted.

Definition two_sorter_Interface bitSize
  := combinationalInterface "two_sorter"
     (mkPort "inputs" (BitVec (BitVec Bit bitSize) 2))
     (mkPort "sorted" (BitVec (BitVec Bit bitSize) 2))
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

Lemma two_sorter_correct: forall (n m: nat) (a b: Bvector m),
      combinational (twoSorter [a; b]) = twoSorterSpec [a; b].
Proof.
Abort. (* Proof unfolds in a complicated way. *)

(*

TODO: Fix type error:
Error:
In environment
unpair : forall n : nat, t (nat * nat) n -> t nat (2 * n)
n : nat
v : t (nat * nat) n
n' : nat
v0 : t (nat * nat) (S n')
x : nat * nat
xs : t (nat * nat) n'
a : nat
b : nat
The term "a :: b :: unpair n' xs" has type "t nat (S (S (2 * n')))"
while it is expected to have type "t nat (2 * S n')".

Fixpoint unpair {n} (v: Vector.t (nat * nat) n) : Vector.t nat (2*n) :=
  match n, v return Vector.t nat (2*n) with
  | O, vv => []
  | S n', vv => let (x, xs) := Vector.uncons v in
                let (a, b) := x in
                a :: b :: unpair xs
  end.

Definition riffle {n} (v: Vector.t nat (2*n)) : Vector.t nat (2*n) :=
  let '(a, b) := halveV v in
  let abz := vcombine a b in
  unpair abz.

*)