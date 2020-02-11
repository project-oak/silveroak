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
From Coq Require Import Lists.List.
Require Import Coq.Lists.List Coq.Bool.Bool.
From Coq Require Import ZArith.
Require Import Lia.
Import ListNotations.

Scheme Equality for list.

Require Import ExtLib.Structures.Monads.

Require Import Cava.
Require Import FullAdder.
Require Import FullAdderNat.
Require Import UnsignedAdder.
Require Import BitVector.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* This module is designed for use for verification and testing and not
   SystemVerilog extraction.
*)

(****************************************************************************)


Lemma addN_bheaviour : forall (ab : list (bool * bool)), 
                       bits_to_nat (combinational (adder false ab)) =
                       (bits_to_nat (map fst ab)) + (bits_to_nat (map snd ab)).
Proof.
  unfold combinational.
  unfold fst.
  unfold adder.
  unfold unsignedAdder.
  unfold col.
Abort.

