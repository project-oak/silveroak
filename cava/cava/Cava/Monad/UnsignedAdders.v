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

(* A codification of the Lava embedded DSL develope for Haskell into
   Coq for the specification, implementaiton and formal verification of
   circuits. Experimental work, very much in flux, as Satnam learns Coq!
*)

From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.


Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.

Require Import Nat Arith Lia.


(******************************************************************************)
(* An adder with two inputs that must be the same length.                     *)
(******************************************************************************)

Definition adderFixed {m bit} `{Cava m bit} {inputSize : nat}
                      (sumSize : nat)
                      (a : (Vector.t bit inputSize))
                      (b : (Vector.t bit inputSize))
                      : m (Vector.t bit sumSize) :=
  a_plus_b <- unsignedAdd sumSize a b ;;
  ret a_plus_b.

(******************************************************************************)
(* A three input adder.                                                       *)
(******************************************************************************)

Definition adder_3input {m bit} `{Cava m bit} {inputSize : nat}
                        (sumSize : nat)
                        (a : (Vector.t bit inputSize))
                        (b : (Vector.t bit inputSize))
                        (c : (Vector.t bit inputSize))
                        : m (Vector.t bit sumSize) :=
  a_plus_b <- unsignedAdd sumSize a b ;;
  sum <- unsignedAdd sumSize a_plus_b c ;;
  ret sum.

Lemma mod_plus_mod: forall a b c n, n > 0 ->
                    ((a + b) mod n + c) mod n = (a + b + c) mod n.
Proof.
  intros.
  rewrite Nat.add_mod_idemp_l.
  - reflexivity.
  - lia.
Qed.

Lemma two_p_gt_0: forall n, 2^n > 0.
Proof.
  intros.
  induction n.
  - simpl. lia.
  - rewrite Nat.pow_succ_r.
    + lia.
    + lia.
Qed.

Lemma add3_behaviour : forall {inputSize : nat} (sumSize : nat)
                       (av : Bvector inputSize)
                       (bv : Bvector inputSize)
                       (cv : Bvector inputSize),
                       let a := bitvec_to_nat av in
                       let b := bitvec_to_nat bv in
                       let c := bitvec_to_nat cv in
                       bitvec_to_nat (combinational (adder_3input sumSize av bv cv))
                         = (a + b + c) mod 2^sumSize.
Proof.
  intros. unfold combinational. unfold adder_3input. simpl.
  do 2 rewrite nat_of_bits_sized_n.
  fold a b c.
  rewrite mod_plus_mod.
  - reflexivity.
  - apply two_p_gt_0.
Qed.

