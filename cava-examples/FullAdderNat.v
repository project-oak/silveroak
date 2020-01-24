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

(* Definitions used for nat level proofs about the full adder which are kept
   separate because they are not used for extraction to SystemVerilog.
*)

From Coq Require Import Bool.Bool. 
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Require Import Nat Arith Lia.
Import ListNotations.

Require Import Hask.Control.Monad.

Require Import Cava.

Local Open Scope list_scope.
Local Open Scope monad_scope.

Require Import Cava.
Require Import FullAdder.
Require Import BitVector.

Lemma halfAdderNat :
  forall (a : bool) (b : bool),
  let (part_sum, carry_out) := combinational (halfAdder a b) in
  bits_to_nat [part_sum; carry_out] = Nat.b2n a + Nat.b2n b.
Proof.
  intros a b.
  case a, b.
  all: reflexivity.
Qed.
  
Lemma fullAdderNat :
  forall (a : bool) (b : bool) (cin : bool),
  let (sum, carry_out) := combinational (fullAdder a b cin) in
  bits_to_nat [sum; carry_out] = Nat.b2n a + Nat.b2n b + Nat.b2n cin.
Proof.
  intros.
  case a, b, cin.
  all: reflexivity.
Qed.