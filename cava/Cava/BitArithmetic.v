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

(* Bit-vector arithmetic operations for Cava. *)

From Coq Require Import Bool.Bool. 
From Coq Require Import Lists.List.
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
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
    
(******************************************************************************)
(* Functions useful for Vector operations                                     *)
(******************************************************************************)

Fixpoint bitvec_to_nat {n : nat} (bits : Bvector n) : nat :=
  match n, bits with
  | 0, _ => 0
  | S n', bv => Nat.b2n (Blow n' bv) + 2 * (bitvec_to_nat (Bhigh n' bv))
  end.

Definition bv3_0 : Bvector 3 := of_list [false; false; false].
Example bv3_0_ex : bitvec_to_nat bv3_0 = 0.
Proof. reflexivity. Qed.

Definition bv3_1 : Bvector 3 := of_list [true; false; false].
Example bv3_1_ex : bitvec_to_nat bv3_1 = 1.
Proof. reflexivity. Qed.

Definition bv3_2 : Bvector 3 := of_list [false; true; false].
Example bv3_2_ex : bitvec_to_nat bv3_2 = 2.
Proof. reflexivity. Qed.


Fixpoint nat_to_bitvec (n : nat) (v : nat) : Bvector n :=
  match n with
  | 0    => Bnil
  | S n' => Bcons (testbit v 0) n' (nat_to_bitvec n' (div2 v))
  end.

Example bv3_0_exrev : nat_to_bitvec 3 0 = bv3_0.
Proof. reflexivity. Qed.

Example bv3_1_exrev : nat_to_bitvec 3 1 = bv3_1.
Proof. reflexivity. Qed.

Example bv3_2_exrev : nat_to_bitvec 3 2 = bv3_2.
Proof. reflexivity. Qed.

(* Vector version of list seq *)
Fixpoint vec_seq (a b : nat) : Vector.t nat b :=
  match b with
  | 0 => Vector.nil nat
  | S b' => Vector.cons nat a b' (vec_seq (a + 1) b')
  end.

(* Vector version of replicate *)
Fixpoint replicate_vec {A : Type} (n : nat) (v : A) : Vector.t A n :=
  match n with
  | 0    => Vector.nil A
  | S n' => Vector.cons A v n' (replicate_vec n' v)
  end.

(******************************************************************************)
(* Functions useful for examples and tests                                    *)
(******************************************************************************)

Definition fromVec := List.map Nat.b2n.
Definition toVec := List.map nat2bool.