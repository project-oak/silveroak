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

(* A codification of the Lava embedded DSL develope for Haskell into
   Coq for the specification, implementaiton and formal verification of
   circuits. Experimental work, very much in flux, as Satnam learns Coq!
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Arith.PeanoNat.
Require Import Omega.

From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.
Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Monad.UnsignedAdders.

Set Implicit Arguments.

Definition v0 := nat_to_list_bits_sized 8  4.
Definition v1 := nat_to_list_bits_sized 8 17.
Definition v2 := nat_to_list_bits_sized 8  6.
Definition v3 := nat_to_list_bits_sized 8  3.

Local Open Scope nat_scope.
Local Open Scope string_scope.

Definition halve {A} (l : list A) : list A * list A :=
  let mid := (length l) / 2 in
  (firstn mid l, skipn mid l).

Local Close Scope nat_scope.

Fixpoint adderTree {m bit} `{Cava m bit} (n : nat) (v: list (list bit)) : m (list bit) :=
  match n with
  | O => match v with
         | [a; b] => unsignedAdd a b
         | _ => ret [] (* Error case *)
         end
  | S n' => let '(vL, vH) := halve v in
            aS <- adderTree n' vL ;;
            bS <- adderTree n' vH ;;
            sum <- unsignedAdd aS bS ;;
            ret sum
  end.
 
(* An adder tree with 2 inputs. *)

Definition adderTree2 {m bit} `{Cava m bit} (v : list (list bit)) : m (list bit)
  := adderTree 0 v.

Definition v0_v1 := [v0; v1].
Definition v0_plus_v1 : list bool := combinational (adderTree2 v0_v1).
Example sum_vo_v1 : list_bits_to_nat v0_plus_v1 = 21.
Proof. reflexivity. Qed.

(* An adder tree with 4 inputs. *)

Definition adderTree4 {m bit} `{Cava m bit} (v : list (list bit)) : m (list bit)
  := adderTree 1 v.

Definition v0_v1_v2_v3 := [v0; v1; v2; v3].
Definition adderTree4_v0_v1_v2_v3 : list bool := combinational (adderTree4 v0_v1_v2_v3).
Example sum_v0_v1_v2_v3 : list_bits_to_nat (combinational (adderTree4 v0_v1_v2_v3)) = 30.
Proof. reflexivity. Qed.

Local Open Scope nat_scope.

Definition adder_tree4_8Interface
  := mkCircuitInterface "adder_tree4_8"
     (Tuple2 (Tuple2 (One ("a", BitVec [8])) (One ("b", BitVec [8])))
             (Tuple2 (One ("c", BitVec [8])) (One ("d", BitVec [8]))))
     (One ("sum", BitVec [11]))
     [].

Definition adder_tree4_8Netlist
  := makeNetlist adder_tree4_8Interface
    (fun '((a, b), (c, d)) => adderTree4 [a; b; c; d]).



