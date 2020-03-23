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

(* Bit-vector operations for Cava.
*)

From Coq Require Import Bool.Bool. 
From Coq Require Import Lists.List.
Require Import Nat Arith.
Require Import Omega.
From Coq Require Import btauto.Btauto.
Require Import Nat Arith Lia.
From Coq Require Import Arith.PeanoNat.

Import ListNotations.

Local Open Scope list_scope.

(* Convert a bit-vector (LSB at first element) to a natural number. *)

Fixpoint bits_to_nat (bits : list bool) : nat :=
  match bits with
  | [] => 0
  | b::bs => Nat.b2n b + 2 * (bits_to_nat bs)
  end.

Example b2n_empty : bits_to_nat [] = 0.
Proof. reflexivity. Qed.

Example b2n_0 : bits_to_nat [false] = 0.
Proof. reflexivity. Qed.

Example b2n_1 : bits_to_nat [true] = 1.
Proof. reflexivity. Qed.

Example b2n_10 : bits_to_nat [true; false] = 1.
Proof. reflexivity. Qed.

Example b2n_01 : bits_to_nat [false; true] = 2.
Proof. reflexivity. Qed.

Example b2n_11 : bits_to_nat [true; true] = 3.
Proof. reflexivity. Qed.

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

Fixpoint nat_to_bits (n : nat) (v : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => testbit v 0 :: nat_to_bits n' (div2 v)
  end.

Example n2b_0_1 : nat_to_bits 1 0 = [false].
Proof. reflexivity. Qed.

Example n2b_0_2 : nat_to_bits 2 0 = [false; false].
Proof. reflexivity. Qed.

Example n2b_0_3 : nat_to_bits 3 0 = [false; false; false].
Proof. reflexivity. Qed.

Example n2b_1_1 : nat_to_bits 1 1 = [true].
Proof. reflexivity. Qed.

Example n2b_2_1: nat_to_bits 2 1 = [true; false].
Proof. reflexivity. Qed.

Example n2b_2_2 : nat_to_bits 2 2 = [false; true].
Proof. reflexivity. Qed.

Example n2b_2_3 : nat_to_bits 2 3 = [true; true].
Proof. reflexivity. Qed.

(*
Lemma twice : forall (n : nat), n + n = 2 * n.
Proof.
  lia.
Qed.

Lemma even_sn : forall (n : nat), even (S n) = odd (S n + 1).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - unfold even.
Abort.

Lemma odd_even : forall (n : nat), odd (n + 1) = even n.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
Abort.

Lemma odd_2n_plus_1 : forall (n : nat), odd (2 * n + 1) = true.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
Abort.

Lemma first_bit: forall (a : bool) (a0 : list bool),
               nat_to_bits (length (a :: a0)) (bits_to_nat (a :: a0)) =
               a :: nat_to_bits (length a0) (bits_to_nat a0).
Proof.
  intros.
  destruct a.
  - simpl. rewrite plus_0_r.
  - simpl. rewrite plus_0_r. unfold Nat.b2n. unfold odd. unfold negb.
    destruct a.
    + simpl. reflexivity.
    + simpl. reflexivity.
Abort.
*)

Lemma bits_to_from_nat : forall (a : list bool),
                         length a > 0 ->
                         nat_to_bits (length a) (bits_to_nat a) = a.  
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
Abort.
    

(******************************************************************************)
(* Functions useful for examples and tests                                    *)
(******************************************************************************)

Definition fromVec := map Nat.b2n.
Definition toVec := map nat2bool.