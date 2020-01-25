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

Require Import Hask.Control.Monad.

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

Definition fromVec := map Nat.b2n.

Definition toVec := map nat2bool.


(****************************************************************************)

Definition v1 := [0;1;0;0;0;0;0;0].
Definition v2 := [1;0;0;0;0;0;0;0].

Definition eval_unsignedAdder a b :=
  fromVec (combinational (adder false (combine (toVec a) (toVec b)))).

Example v1_plus_v2 : eval_unsignedAdder v1 v2 = [1; 1; 0; 0; 0; 0; 0; 0; 0].
Proof. reflexivity. Qed.

(****************************************************************************)

Definition v0 : list nat := [].

Example v0_plus_v0 : eval_unsignedAdder v0 v0 = [0].
Proof. reflexivity. Qed.

(****************************************************************************)

Definition v3 := [1;1;1;1;1;1;1;1].
Definition v4 := [1;0;0;0;0;0;0;0].

Example v3_plus_v4 : eval_unsignedAdder v3 v4 = [0; 0; 0; 0; 0; 0; 0; 0; 1].
Proof. reflexivity. Qed.

(****************************************************************************)

Definition v5 := [1;1;1;1;1;1;1;1].
Definition v6 := [1;1;1;1;1;1;1;1].

Example v5_plus_v6 : eval_unsignedAdder v5 v6 = [0; 1; 1; 1; 1; 1; 1; 1; 1].
Proof. reflexivity. Qed.

(****************************************************************************)

Definition addN {m t} `{CavaTop m t} ab :=
  sum_carry <- unsignedAdder false ab;
  let sum := fst sum_carry in
  let carry := snd sum_carry in
  return_ (sum ++ [carry]).


Lemma addN_bheaviour : forall (ab : list (bool * bool)), 
                       bits_to_nat (combinational (addN ab)) =
                       (bits_to_nat (map fst ab)) + (bits_to_nat (map snd ab)).
Proof.
Abort.

