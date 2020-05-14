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

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Syntax.
Require Import Cava.Arrow.Instances.Combinational.

Definition mux2_1' `{Cava} 
: Kappa (bit ** (bit ** bit) ** unit) bit :=  
<[ \ sel ab =>
   let a = fst' ab in
   let b = snd' ab in
   let sel_a = !and_gate sel a in
   let inv_sel = !not_gate sel in
   let sel_b = !and_gate inv_sel b in
   let sel_out = !or_gate sel_a sel_b in
   sel_out
]>.

Open Scope source.

Definition mux2_1 `{Cava} : (bit ** (bit ** bit) ** unit) ~> bit
  := Closure_conversion mux2_1'.
