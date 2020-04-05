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

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Monad.Cava.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* NAND gate example. Fist, let's define an overloaded NAND gate
   description. *)

Definition nand2_gate {m t} `{Cava m t} := and2 >=> inv.

Definition nand2Top :=
  setModuleName "nand2" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  c <- nand2_gate (a, b) ;;
  outputBit "c" c.

Definition nand2Netlist := makeNetlist nand2Top.

(* A proof that the NAND gate implementation is correct. *)
Lemma nand2_behaviour : forall (a : bool) (b : bool),
                        combinational (nand2_gate (a, b)) = negb (a && b).
Proof.
  auto.
Qed.

(* A proof that the sequential NAND gate implementation is correct. *)
Lemma nand2_seq_behaviour : forall (a : list bool) (b : list bool),
                            sequential (nand2_gate (a, b)) = map (fun (i : bool * bool) => let (a, b) := i in
                                                             negb (a && b)) (combine a b).
Proof.
  intros.
  unfold sequential.
  unfold unIdent.
  simpl.
  rewrite map_map.
  rewrite map_ext_in_iff.
  intros.
  now destruct a0.  
Qed.

(* An exhuastive proof by analyzing all four cases. *)
Example nand_00 : combinational (nand2_gate (false, false)) = true.
Proof. reflexivity. Qed.

Example nand_01 : combinational (nand2_gate (false, true)) = true.
Proof. reflexivity. Qed.

Example nand_10 : combinational (nand2_gate (true, false)) = true.
Proof. reflexivity. Qed.

Example nand_11 : combinational (nand2_gate (true, true)) = false.
Proof. reflexivity. Qed.

(* A nand-gate with registers after the AND gate and the INV gate. *)

Definition pipelinedNAND {m t} `{Cava m t}
  := nand2_gate >=> delayBit >=> inv >=> delayBit.

Definition pipelinedNANDTop :=
  setModuleName "pipelinedNAND" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  c <- pipelinedNAND (a, b) ;;
  outputBit "c" c.

Definition pipelinedNANDNetlist := makeNetlist pipelinedNANDTop.
