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

From Coq Require Import ZArith.
From Coq Require Import ZArith.BinInt.
From Coq Require Import PArith.BinPos.
From Coq Require Import Numbers.NatInt.NZPow.
Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.

Require Import Nat Arith Lia.

From Coq Require Import Lists.List.
Import ListNotations.

(******************************************************************************)
(* A three input adder.                                                       *)
(******************************************************************************)

Definition adder_3input {m bit} `{Cava m bit} (sumSize : nat)
                        (a : list bit) (b : list bit) (c : list bit)
                        : m (list bit) :=
  a_plus_b <- unsignedAdd sumSize a b ;;
  sum <- unsignedAdd sumSize a_plus_b c ;;
  ret sum.

Open Scope N_scope.

Lemma mod_plus_mod: forall a b c n, n > 0 ->
                    ((a + b) mod n + c) mod n = (a + b + c) mod n.
Proof.
  intros.
  rewrite N.add_mod_idemp_l.
  - reflexivity.
  - lia.
Qed.

Lemma two_p_gt_0: forall n, 2^n > 0.
Proof.
  intros.
  induction n.
  - reflexivity.
(* Ugh, what is the N equivalent of Nat.pow_succ_r ? *)
Admitted.

Lemma add3_behaviour : forall (sumSize : nat)
                       (av : list bool)
                       (bv : list bool)
                       (cv : list bool),
                       let a := list_bits_to_nat av in
                       let b := list_bits_to_nat bv in
                       let c := list_bits_to_nat cv in
                       list_bits_to_nat (combinational (adder_3input sumSize av bv cv))
                         = (a + b + c) mod 2^(N.of_nat sumSize).
Proof.
  intros. unfold combinational. unfold adder_3input. simpl.
  do 2 rewrite nat_of_list_bits_sized.
  fold a b c.
  rewrite mod_plus_mod.
  - reflexivity.
  - apply two_p_gt_0.
Qed.

