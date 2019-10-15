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

Require Import Cava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.

Definition oneBitAdder (cinab : cava Bit * (cava Bit * cava Bit)) : cava Bit * cava Bit
  := let (cin, ab) := cinab in
     let (a, b) := ab in
     let ps := Fork2 (Xor2 (a, b)) in
     let partSum1 := Fst ps in
     let partSum2 := Snd ps in
     let sum := Xorcy (partSum1, cin) in
     let cout := Muxcy (partSum2, (a, cin)) in
       (sum, cout).

Definition oneBitAdder_top
  := let a := Signal "a" in
     let b := Signal "b" in
     let cin := Signal "cin" in
     let (sum, cout) := oneBitAdder (cin, (a, b)) in
       [Output "sum" sum; Output "cout" cout].