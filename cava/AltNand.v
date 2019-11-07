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

Require Import AltCava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Program.Basics.
Local Open Scope program_scope.
Local Open Scope string_scope.
Set Implicit Arguments.


(* A sample simple circuit: a NAND gate built from an AND2 gate and an INV gate *)
Definition nandGate := and2 ⟼ inv.

(* A trivial proof that nandGate has the behaviour of a NAND gate. *)
Lemma nandGate_combinational :
  forall (a b : bool), cavaCombinational nandGate (a, b) = negb (a && b).
auto.
Qed.

Definition nandGateTop : cava (Tuple2 Bit Bit) Bit
  := (Input "a" ‖ Input "b") ⟼ nandGate ⟼ Output "c".

Definition nandGatePipelined : cava (Tuple2 Bit Bit) Bit
  := (Input "a" ‖ Input "b") ⟼ and2 ⟼ Delay ⟼ inv ⟼ Delay ⟼ Output "c".
