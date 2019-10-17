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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Require Import Program.Basics.
Local Open Scope program_scope.
Set Printing All.
Set Implicit Arguments.

Inductive signal : Set :=
  | Bit : signal
  | Tuple2 : signal -> signal -> signal.

Inductive cava : signal -> signal -> Set :=
  | Input : string -> cava Bit Bit
  | Output : string -> cava Bit Bit
  | Inv : cava Bit Bit
  | And2 : cava (Tuple2 Bit Bit) Bit
  | Xor2 : cava (Tuple2 Bit Bit) Bit
  | Xorcy : cava (Tuple2 Bit Bit) Bit
  | Muxcy : cava (Tuple2 Bit (Tuple2 Bit Bit)) Bit
  | Delay : forall A : signal, cava A A
  | Compose : forall A B C : signal, cava A B -> cava B C -> cava A C
  | Par2 : forall A B C D : signal, cava A C -> cava B D ->
                                  cava (Tuple2 A C) (Tuple2 B D).

Check Compose Inv Inv : cava Bit Bit.
Check Compose And2 Inv : cava (Tuple2 Bit Bit) Bit.
Check Compose Inv (Delay Bit) : cava Bit Bit.

Notation " f ⟼ g " := (Compose f g)
  (at level 39, right associativity) : program_scope.

Notation " a ‖ b " := (Par2 a b)
  (at level 45, right associativity) : program_scope.

