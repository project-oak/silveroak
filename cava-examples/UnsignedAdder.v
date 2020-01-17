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

Require Import Hask.Control.Monad.

Require Import Cava.
Require Import FullAdder.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* An unsigned addder which takes two size N bit-vectors and a carry in
   and returns a sized N+1 result which is the addition of the two
   input vectors and carry in.
*)

Definition unsignedAdder {m bit} `{Cava m bit} := col fullAdderFC.

(* A module definition for an 8-bit adder for SystemVerilog netlist
   generation.
*)

Definition adder8Top {m t} `{CavaTop m t} :=
  setModuleName "adder8" ;;
  a <- inputVectorTo0 8 "a" ;
  b <- inputVectorTo0 8 "b" ;
  cin <- inputBit "cin" ;
  sum_cout <- unsignedAdder cin (combine a b) ;
  let sum := fst sum_cout in
  let cout := snd sum_cout in
  outputVectorTo0 sum "sum" ;;
  outputBit "cout" cout.

Definition adder8Netlist := makeNetlist adder8Top.

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

Definition toVec := map nat2bool.

Definition bool2nat (b : bool) : nat :=
  match b with
  | false => 0
  | true => 1
  end.

Definition fromVec := map bool2nat.

Definition v1 := [0;1;0;0;0;0;0;0].
Definition v2 := [1;0;0;0;0;0;0;0].


Definition eval_unsignedAdder a b :=
  let sum_carry := combinational (unsignedAdder false (combine (toVec a) (toVec b))) in
  let sum := fst sum_carry in
  let carry := snd sum_carry in
  (fromVec sum, bool2nat carry).

Compute (eval_unsignedAdder v1 v2).

Definition v3 := [1;1;1;1;1;1;1;1].
Definition v4 := [1;0;0;0;0;0;0;0].

Compute (eval_unsignedAdder v3 v4).

Definition v5 := [1;1;1;1;1;1;1;1].
Definition v6 := [1;1;1;1;1;1;1;1].

Compute (eval_unsignedAdder v5 v6).