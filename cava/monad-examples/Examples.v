(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
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
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* Experiments with the primitive Cava gates. *)

Example inv_false : combinational (inv false) = true.
Proof. reflexivity. Qed.

Example inv_true  : combinational (inv true) = false.
Proof. reflexivity. Qed.

Example and_00 : combinational (and2 (false, false)) = false.
Proof. reflexivity. Qed.

Example and_11 : combinational (and2 (true, true)) = true.
Proof. reflexivity. Qed.

(* Unsigned addition examples. *)

Definition bv4_0  := nat_to_bitvec_sized 4  0.
Definition bv4_1  := nat_to_bitvec_sized 4  1.
Definition bv4_2  := nat_to_bitvec_sized 4  2.
Definition bv4_3  := nat_to_bitvec_sized 4  3.
Definition bv4_15 := nat_to_bitvec_sized 4 15.

Definition bv5_0  := nat_to_bitvec_sized 5  0.
Definition bv5_3  := nat_to_bitvec_sized 5  3.
Definition bv5_16 := nat_to_bitvec_sized 5 16.
Definition bv5_30 := nat_to_bitvec_sized 5 30.

(* Check 0 + 0 = 0 *)
Example add_0_0 : combinational (unsignedAdd bv4_0 bv4_0) = bv5_0.
Proof. reflexivity. Qed.

(* Check 1 + 2 = 3 *)
Example add_1_2 : combinational (unsignedAdd bv4_1 bv4_2) = bv5_3.
Proof. reflexivity. Qed.

(* Check 15 + 1 = 16 *)
Example add_15_1 : combinational (unsignedAdd bv4_15 bv4_1) = bv5_16.
Proof. reflexivity. Qed.

(* Check 15 + 15 = 30 *)
Example add_15_15 : combinational (unsignedAdd bv4_15 bv4_15) = bv5_30.
Proof. reflexivity. Qed.

(* An adder example. *)

Definition adder4Top : state CavaState (Vector.t N 5) :=
  setModuleName "adder4" ;;
  a <- inputVectorTo0 4 "a" ;;
  b <- inputVectorTo0 4 "b" ;;
  sum <- unsignedAdd a b ;;
  outputVectorTo0 5 sum "sum".

Definition adder4Netlist := makeNetlist adder4Top.

(* An contrived example of loopBit *)

Definition loopedNAND {m bit} `{Cava m bit}  := loopBit (second delayBit >=> nand2 >=> fork2).

Definition loopedNANDTop : state CavaState N :=
  setModuleName "loopedNAND" ;;
  a <- inputBit "a" ;;
  b <- loopedNAND a ;;
  outputBit "b" b.

Definition loopedNANDNetlist := makeNetlist loopedNANDTop.

Fixpoint loopedNAND_spec' (i : list bool) (state : bool) : list bool :=
  match i with
  | [] => []
  | x::xs => let newOutput := negb (x && state) in
             newOutput :: loopedNAND_spec' xs newOutput
  end.

(*
Definition loopedNAND_spec (i : list bool) : list bool := loopedNAND_spec' i false.

Lemma peel_list : forall (a : bool) (x y : list bool),
                  a::x = a::y <-> x = y.
Proof.
  intros.
  destruct x.


Lemma noopedNAND_behaviour : forall (a : list bool),
                             sequential (loopedNAND a) = loopedNAND_spec a.
Proof.
  intros.
  unfold sequential.
  unfold unIdent.
  simpl.
  unfold loopedNAND_spec.
  induction a.
  auto.
  simpl.
  rewrite peel_list.
*)

  
