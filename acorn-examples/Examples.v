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

(* Experiments with the primitives that form the core of Cava. *)

Require Import Coq.Lists.List.
Require Import Cava.Cava.
Import ListNotations.

(* Experiments with the primitive Cava gates. *)

Example inv_false : inv false = true.
Proof. reflexivity. Qed.

Example inv_true  : inv true = false.
Proof. reflexivity. Qed.

Example and_00 : and2 (false, false) = false.
Proof. reflexivity. Qed.

Example and_11 : and2 (true, true) = true.
Proof. reflexivity. Qed.
