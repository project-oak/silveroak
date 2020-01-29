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

(* Bit-vector operations for Cava.
*)

From Coq Require Import Bool.Bool. 
From Coq Require Import Lists.List.
Require Import Nat Arith.
Import ListNotations.

Local Open Scope list_scope.

(* Convert a bit-vector (LSB at first element) to a natural number. *)

Fixpoint bits_to_nat (bits : list bool) : nat :=
  match bits with
  | [] =>  0
  | b::bs => Nat.b2n b + 2 * bits_to_nat bs
  end.

Compute bits_to_nat [false; true; true].

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.