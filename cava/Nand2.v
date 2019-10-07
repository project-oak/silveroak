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
Require Import Program.Basics.
Local Open Scope program_scope.

Definition nand2_pipelined := Delay ∘ Inv ∘ Delay ∘ And2.

Definition and2_pipelined_top
  := Output "o" (nand2_pipelined (Signal "i0", Signal "i1")).

Definition nand2_combinational := compose Inv And2.
