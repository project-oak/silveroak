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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.BitVector.
Require Import FullAdder.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* An unsigned addder which takes two size N bit-vectors and a carry in
   and returns a size N sum and a carry out which is the addition of the two
   input vectors and carry in.
*)

Definition unsignedAdder {m bit} `{Cava m bit} := col fullAdderFC.

(****************************************************************************)
(* A few tests to check the unsigned adder. *)

Definition v0   := [0;0;0;0;0;0;0;0].
Definition v1   := [1;0;0;0;0;0;0;0].
Definition v2   := [0;1;0;0;0;0;0;0].
Definition v3   := [1;1;1;1;1;1;1;1].
Definition v4   := [1;0;0;0;0;0;0;0].
Definition v5   := [1;1;1;1;1;1;1;1].
Definition v6   := [1;1;1;1;1;1;1;1].
Definition v255 := [1;1;1;1;1;1;1;1].

Definition eval_unsignedAdder cin a b :=
  let '(sum, carry)
    := combinational
       (unsignedAdder (nat2bool cin) (combine (toVec a) (toVec b))) in
  (fromVec sum, Nat.b2n carry).

Example v1_plus_v2 : eval_unsignedAdder 0 v1 v2 = ([1; 1; 0; 0; 0; 0; 0; 0], 0).
Proof. reflexivity. Qed.

Example v0_plus_v1 : eval_unsignedAdder 0 v0 v1 = ([1; 0; 0; 0; 0; 0; 0; 0], 0).
Proof. reflexivity. Qed.

Example v255_plus_v1 : eval_unsignedAdder 0 v255 v1 = ([0; 0; 0; 0; 0; 0; 0; 0], 1).
Proof. reflexivity. Qed.

Example v255_plus_v0_cin1 : eval_unsignedAdder 1 v255 v0 = ([0; 0; 0; 0; 0; 0; 0; 0], 1).
Proof. reflexivity. Qed.

Example v255_plus_255_cin1 : eval_unsignedAdder 1 v255 v255 = ([1; 1; 1; 1; 1; 1; 1; 1], 1).
Proof. reflexivity. Qed.

Example v3_plus_v4 : eval_unsignedAdder 0 v3 v4 = ([0; 0; 0; 0; 0; 0; 0; 0], 1).
Proof. reflexivity. Qed.

Example v5_plus_v6 : eval_unsignedAdder 0 v5 v6 = ([0; 1; 1; 1; 1; 1; 1; 1], 1).
Proof. reflexivity. Qed.

(****************************************************************************)
(* A module definition for an 8-bit adder for SystemVerilog netlist
   generation.
*)

Definition adder8Top :=
  setModuleName "adder8" ;;
  a <- inputVectorTo0 8 "a" ;;
  b <- inputVectorTo0 8 "b" ;;
  cin <- inputBit "cin" ;;
  '(sum, cout) <- unsignedAdder cin (combine a b) ;;
  outputVectorTo0 sum "sum" ;;
  outputBit "cout" cout.

Definition adder8Netlist := makeNetlist adder8Top.

(****************************************************************************)
(* Adder with bit-growth at output sum (so no carry out                     *)
(****************************************************************************)

Definition adder {m bit} `{Cava m bit} cin ab :=
  '(sum, carry) <- unsignedAdder cin ab ;;
  ret (sum ++ [carry]).

(****************************************************************************)
