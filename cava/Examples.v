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

(* A codification of the Lava embedded DSL develope for Haskell into
   Coq for the specification, implementaiton and formal verification of
   circuits. Experimental work, very much in flux, as Satnam learns Coq!
*)

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* Experiments with the primitive Cava gates. *)

Example inv_false : combinational (not_gate false) = true.
Proof. reflexivity. Qed.

Example inv_true  : combinational (not_gate true) = false.
Proof. reflexivity. Qed.

Example and_00 : combinational (and_gate [false; false]) = false.
Proof. reflexivity. Qed.

Example and_11 : combinational (and_gate [true; true]) = true.
Proof. reflexivity. Qed.

Eval cbv in (execState (not_gate (2%Z)) (initStateFrom 3)).

(* NAND gate example. Fist, let's define an overloaded NAND gate
   description. *)

Definition nand2 {m bit} `{Cava m bit} := and_gate >=> not_gate.

(* Simulate the NAND gate circuit using the Bool interpretation. *)
Example nand_00 : combinational (nand2 [false; false]) = true.
Proof. reflexivity. Qed.

Example nand_11 : combinational (nand2 [true; true]) = false.
Proof. reflexivity. Qed.

(* Generate a circuit graph representation for the NAND gate using the
   netlist interpretatin. *)
Eval cbv in (execState (nand2 [2%Z; 3%Z]) (initStateFrom 4)).

Definition nand2Top : state CavaState Z :=
  setModuleName "nand2" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  c <- nand2 [a; b] ;;
  outputBit "c" c.

(* Generate a netlist containing the port definitions. *)
Eval cbv in (execState nand2Top initState).

Definition nand2Netlist := makeNetlist nand2Top.

(* A proof that the NAND gate implementation is correct. *)
Lemma nand2_behaviour : forall (a : bool) (b : bool),
                        combinational (nand2 [a; b]) = negb (a && b).
Proof.
  auto.
Qed.

(* An contrived example of loopBit *)

Definition nand2Gate {m bit} `{Cava m bit} (ab : bit * bit) : m bit :=
  nand2 [fst ab; snd ab].

Definition loopedNAND := loopBit (second delayBit >=> nand2Gate >=> fork2).

Definition loopedNANDTop : state CavaState Z :=
  setModuleName "loopedNAND" ;;
  a <- inputBit "a" ;;
  b <- loopedNAND a ;;
  outputBit "b" b.

Definition loopedNANDNetlist := makeNetlist loopedNANDTop.
