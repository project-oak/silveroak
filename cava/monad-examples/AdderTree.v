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

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import NArith.
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.

Require Import Nat Arith Lia.

Local Open Scope list_scope.
Local Open Scope monad_scope.

Set Implicit Arguments.


Definition adder_3in {m bit} `{Cava m bit} {aL bL cL : nat}
                     (a : (Vector.t bit aL))
                     (b : (Vector.t bit bL))
                     (c : (Vector.t bit cL))
                     : m (Vector.t bit (max (max aL bL + 1) cL + 1)) :=
  a_plus_b <- unsignedAdd a b ;;
  sum <- unsignedAdd a_plus_b c ;;
  ret sum.


Definition adder8_3inTop : state CavaState (Vector.t N 10) :=
  setModuleName "adder8_3in" ;;
  a <- inputVectorTo0 8 "a" ;;
  b <- inputVectorTo0 8 "b" ;;
  c <- inputVectorTo0 8 "c" ;;
  sum <- adder_3in a b c ;;
  outputVectorTo0 10 sum "sum".

Definition adder8_3inNetlist := makeNetlist adder8_3inTop.

Lemma add3_behaviour : forall aL bL cL (av : Bvector aL) (bv : Bvector bL) (cv : Bvector cL),
                       let a := bitvec_to_nat av in
                       let b := bitvec_to_nat bv in
                       let c := bitvec_to_nat cv in
                       bitvec_to_nat (combinational (adder_3in av bv cv)) = a + b + c.
Proof.
  intros. unfold combinational. unfold adder_3in. simpl.
  rewrite nat_of_bits_sized_n. rewrite nat_of_bits_sized_n.
  reflexivity.
Qed.

Lemma max_x_x : forall x, max x x = x.
Proof.
 intro x. induction x. simpl. auto. simpl. rewrite IHx. reflexivity.
Defined.

Definition simplify_max {a n} (x : Vector.t a (max n n + 1)) : Vector.t a (n + 1).
  rewrite max_x_x in x.
  auto.
Defined.

Definition adderFixed {m bit} `{Cava m bit} {l : nat}
                      (a : (Vector.t bit l))
                      (b : (Vector.t bit l))
                      : m (Vector.t bit (l + 1)) :=
  a_plus_b <- unsignedAdd a b ;;
  ret (simplify_max a_plus_b).

Definition adder_fixed_top : state CavaState (Vector.t N 9) :=
  setModuleName "adder_fixed" ;;
  a <- inputVectorTo0 8 "a" ;;
  b <- inputVectorTo0 8 "b" ;;
  sum <- adderFixed a b ;;
  outputVectorTo0 9 sum "sum".

Definition adder_fixedNetlist := makeNetlist adder_fixed_top.

Definition v0 := nat_to_bitvec_sized 8  4.
Definition v1 := nat_to_bitvec_sized 8 17.
Definition v2 := nat_to_bitvec_sized 8  6.
Definition v3 := nat_to_bitvec_sized 8  3.

Example check_fixed: bitvec_to_nat (combinational (adderFixed v0 v1)) = 21.
Proof. reflexivity. Qed.

(* TODO(satnam): track down a library that must contain this lemma. *)
Lemma add_1_r : forall n, S n = n + 1.
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Defined.

(* To create an adder with no bit-growth at the output we need to be able
   to discard the top bit, producing a add-modulo unsigned adder.
*)
Definition discardTopBit {a n} (v : Vector.t a (n+1)) : Vector.t a n.
  apply shiftout.
  rewrite add_1_r.
  auto.
Defined.

Definition adderNoGrowth {m bit} `{C : Cava m bit} {l : nat}
                         (a : (Vector.t bit l))
                         (b : (Vector.t bit l))
                         : m (Vector.t bit l) :=
  a_plus_b <- adderFixed a b ;;
  ret (discardTopBit a_plus_b).

Definition to_n_plus_n {a n} (v : Vector.t a (2*n)) : Vector.t a (n + n).
Proof.
  intros. simpl in v. rewrite <- plus_n_O in v. apply v.
Defined.

Definition halve' {n a} (v : Vector.t a (n+n)) : Vector.t a n * Vector.t a n :=
  splitat n v.

Definition v0_3 : Vector.t (Bvector 8) (2+2) := [v0; v1; v2; v3]%vector.
(* Compute halve' v0_3. *)

Definition halve {n a} (v : Vector.t a (2*n)) : Vector.t a n * Vector.t a n :=
  halve' (to_n_plus_n v).

Fixpoint adderTree {m bit} `{Cava m bit} (n s : nat) (v : Vector.t (Vector.t bit s) (2^(n+1))) : m (Vector.t bit s) :=
  match n, v with
  | O, v2 => adderNoGrowth (hd v2) (hd (tl v2))
  | S n', vR => let '(vL, vH) := halve vR in
                aS <- adderTree n' vL ;;
                bS <- adderTree n' vH ;;
                sum <- adderNoGrowth aS bS ;;
                ret sum
  end.
 
(* An adder tree with 2 inputs each of 8 bits in size. *)

Definition adderTree2_8 {m bit} `{Cava m bit} (v : Vector.t (Vector.t bit 8) 2) : m (Vector.t bit 8)
  := adderTree 0 v.

Definition v2_8 : Vector.t (Bvector 8) 2 := [v0; v1]%vector.
Definition v0_plus_v1 : Bvector 8 := combinational (adderTree2_8 v2_8).
(* Compute v0_plus_v1. *)

Example v0_plus_v1_ex : bitvec_to_nat v0_plus_v1 = 21.
Proof. reflexivity. Qed.

(* An adder tree with 4 inputs each of 8 bits in size. *)

Definition adderTree4_8 {m bit} `{Cava m bit} (v : Vector.t (Vector.t bit 8) 4) : m (Vector.t bit 8)
  := adderTree 1 v.

Definition adder_tree_4_8_top : state CavaState (Vector.t N 8) :=
  setModuleName "adder_tree_4_8" ;;
  a <- inputVectorTo0 8 "a" ;;
  b <- inputVectorTo0 8 "b" ;;
  c <- inputVectorTo0 8 "c" ;;
  d <- inputVectorTo0 8 "d" ;;
  sum <- adderTree4_8 [a; b; c; d]%vector ;;
  outputVectorTo0 8 sum "sum".

Definition adder_tree_4_8Netlist := makeNetlist adder_tree_4_8_top.

Definition v4_8 : Vector.t (Bvector 8) (2^(1+1)) := [v0; v1; v2; v3]%vector.

Definition adderTree4_8_sim : ident (Vector.t bool 8) := adderTree4_8 v4_8.

(* This computation causes Coq to loop.
Compute (combinational adderTree4_8_sim).
*)

(* This computation causes Coq to loop.
Compute (combinational adderTree4_8_sim).
*)

