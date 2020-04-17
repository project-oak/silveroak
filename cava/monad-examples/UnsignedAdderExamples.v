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

From Coq Require Import Ascii String.
From Coq Require Import Bool.Bool.
From Coq Require Import NArith.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.
Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Monad.UnsignedAdders.

(******************************************************************************)
(* Unsigned addition examples.                                                *)
(******************************************************************************)

Definition bv4_0  := nat_to_list_bits_sized 4  0.
Definition bv4_1  := nat_to_list_bits_sized 4  1.
Definition bv4_2  := nat_to_list_bits_sized 4  2.
Definition bv4_3  := nat_to_list_bits_sized 4  3.
Definition bv4_15 := nat_to_list_bits_sized 4 15.

Definition bv5_0  := nat_to_list_bits_sized 5  0.
Definition bv5_3  := nat_to_list_bits_sized 5  3.
Definition bv5_16 := nat_to_list_bits_sized 5 16.
Definition bv5_30 := nat_to_list_bits_sized 5 30.

(* Check 0 + 0 = 0 *)
Example add5_0_0 : combinational (unsignedAdd bv4_0 bv4_0) = bv5_0.
Proof. reflexivity. Qed.

(* Check 1 + 2 = 3 *)
Example add5_1_2 : combinational (unsignedAdd bv4_1 bv4_2) = bv5_3.
Proof. reflexivity. Qed.

(* Check 15 + 1 = 16 *)
Example add5_15_1 : combinational (unsignedAdd bv4_15 bv4_1) = bv5_16.
Proof. reflexivity. Qed.

(* Check 15 + 15 = 30 *)
Example add5_15_15 : combinational (unsignedAdd bv4_15 bv4_15) = bv5_30.
Proof. reflexivity. Qed.

(******************************************************************************)
(* Generate a 4-bit unsigned adder with 5-bit output.                         *)
(******************************************************************************)

Definition adder4Top : state CavaState (list N) :=
  setModuleName "adder4" ;;
  a <- inputVectorTo0 4 "a" ;;
  b <- inputVectorTo0 4 "b" ;;
  sum <- unsignedAdd a b ;;
  outputVectorTo0 5 sum "sum".

Local Open Scope nat_scope.

Definition adder4Interface
  := mkCircuitInterface "adder4"
     (Tuple2 (One ("a", BitVec [4])) (One ("b", BitVec [4])))
     (One ("sum", BitVec [5]))
     [].

Definition adder4Netlist
  := makeNetlist adder4Interface (fun '(a, b) => unsignedAdd a b).

(******************************************************************************)
(* Generate a three input 8-bit unsigned adder with 10-bit output.            *)
(******************************************************************************)

Definition adder8_3inputInterface
  := mkCircuitInterface "adder8_3input"
     (Tuple2 (One ("a", BitVec [8])) (Tuple2 (One ("b", BitVec [8])) (One ("c", BitVec [8]))))
     (One ("sum", BitVec [10]))
     [].

Definition adder8_3inputNetlist
  := makeNetlist adder8_3inputInterface
     (fun '(a, (b, c)) => adder_3input a b c).

(******************************************************************************)
(* An contrived example of loopBit                                            *)
(******************************************************************************)

Definition loopedNAND {m bit} `{Cava m bit}  := loopBit (second delayBit >=> nand2 >=> fork2).

Definition loopedNANDInterface
  := mkCircuitInterface "loopedNAND"
     (One ("a", Bit))
     (One ("b", Bit))
     [].

Definition loopedNANDNetlist := makeNetlist loopedNANDInterface loopedNAND.

Fixpoint loopedNAND_spec' (i : list bool) (state : bool) : list bool :=
  match i with
  | [] => []
  | x::xs => let newOutput := negb (x && state) in
             newOutput :: loopedNAND_spec' xs newOutput
  end.
