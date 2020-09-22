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

From Coq Require Import Bool.Bvector.
From Coq Require Import NArith.Ndigits.
From Coq Require Import ZArith.
Require Import Omega Lia.
Require Import Vector.

(* An n-bit adder *)

Local Open Scope N_scope.

Definition vectorAdd {aWidth bWidth: nat} (cWidth: nat)
                     (a: Bvector aWidth) (b: Bvector bWidth) : Bvector cWidth :=
  let aN := Bv2N aWidth a in
  let bN := Bv2N bWidth b in
  let c := (aN + bN) mod 2^(N.of_nat cWidth) in
  N2Bv_sized cWidth c.

Compute Bv2N (vectorAdd 8 (N2Bv_sized 8 5) (N2Bv_sized 8 12)).
Compute Bv2N (vectorAdd 8 (N2Bv_sized 8 5) (N2Bv_sized 8 254)).

Definition vectorAddGrowth {width: nat}
           (a: Bvector width) (b: Bvector width) :
           Bvector (1 + width) :=
  let aN : N := Bv2N width a in
  let bN : N := Bv2N width b in
  let c : N := aN + bN in
  N2Bv_sized (1 + width) c.

Definition vectorAdd4Growth {width: nat}
                            (a: Bvector width)
                            (b: Bvector width)
                            (c: Bvector width)
                            (d: Bvector width) :
                            Bvector (2 + width) :=
  let a_plus_b := vectorAddGrowth a b in
  let c_plus_d := vectorAddGrowth c d in
  vectorAddGrowth a_plus_b c_plus_d.

Definition vectorAddGrowth2 {aWidth bWidth: nat}
           (a: Bvector aWidth) (b: Bvector bWidth) :
           Bvector (1 + max aWidth bWidth) :=
  let aN : N := Bv2N aWidth a in
  let bN : N := Bv2N bWidth b in
  let c : N := aN + bN in
  N2Bv_sized (1 + max aWidth bWidth) c.

Definition vectorAdd3Growth {aWidth bWidth cWidth: nat}
                            (a: Bvector aWidth)
                            (b: Bvector bWidth)
                            (c: Bvector cWidth) :
                            Bvector (1 + max (1 + max aWidth bWidth) cWidth) :=
  let a_plus_b := vectorAddGrowth2 a b in
  vectorAddGrowth2 a_plus_b c.


Local Open Scope vector_scope.

Lemma bv_p_0 : forall n, Bvector (n + 0) = Bvector n . intros. f_equal. omega. Qed.
Lemma v_p_0 : forall n T, Vector.t T (n + 0) = Vector.t T n . intros. f_equal. omega. Qed.
Lemma bv_p_1 : forall a b, Bvector (a + S b) = Bvector (1 + (a + b)) . intros. f_equal. omega. Qed.

Fixpoint adderTree {n w} (i: Vector.t (Bvector w) (2^n)) : Bvector (w + n).
destruct n.
- rewrite bv_p_0.
  exact (hd i).
- refine ( let (a, b) := splitat (2 ^ n) i in _).
  rewrite v_p_0 in b.
  fold Nat.pow in b.
  refine (
    let lhs := adderTree n _ a in
    let rhs := adderTree n _ b in
    _
  ).
  rewrite bv_p_1.
  exact ( vectorAddGrowth lhs rhs ).
Defined.

Definition i0 : Bvector 8 := N2Bv_sized 8.
Definition v0 : Vector.t (Bvector 8) 1 := [i0].

Compute adderTree v0.