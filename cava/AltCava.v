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


Inductive signal : Type :=
  | Bit : signal
  | Tuple2 : signal -> signal -> signal.

Inductive cava : Set :=
  | Input : string -> cava
  | Output : string -> cava
  | Inv : cava
  | And2 : cava
  | Xor2 : cava
  | Xorcy : cava
  | Muxcy : cava
  | Delay : cava
  | Compose : cava -> cava -> cava
  | Par2 : cava -> cava -> cava.
 
Notation " f ⟼ g " := (Compose f g)
  (at level 39, right associativity) : program_scope.

Notation " a ‖ b " := (Par2 a b)
  (at level 45, right associativity) : program_scope.

