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


Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Section WithCava.
  Context {signal} {combsemantics : Cava signal}
          {seqsemantics: CavaSeq combsemantics}.

  (* NAND gate example. First, let's define an overloaded NAND gate
     description. *)
  Definition nand2_gate : signal Bit * signal Bit -> cava (signal Bit) :=
     and2 >=> inv.

End WithCava.

(******************************************************************************)
(* NAND-gate netlist with tests.                                              *)
(******************************************************************************)

Definition nand2Interface
  := combinationalInterface
    "nand2"
    [mkPort "a" Bit; mkPort "b" Bit]
    [mkPort "c" Bit]
    [].

Definition nand2Netlist := makeNetlist nand2Interface nand2_gate.

(* A proof that the NAND gate implementation is correct. *)
Lemma nand2_behaviour : forall (a : bool) (b : bool),
                        combinational (nand2_gate ([a], [b])) = [negb (a && b)].
Proof.
  auto.
Qed.

(* An exhuastive proof by analyzing all four cases. *)
Example nand_00 : combinational (nand2_gate ([false], [false])) = [true].
Proof. reflexivity. Qed.

Example nand_01 : combinational (nand2_gate ([false], [true])) = [true].
Proof. reflexivity. Qed.

Example nand_10 : combinational (nand2_gate ([true], [false])) = [true].
Proof. reflexivity. Qed.

Example nand_11 : combinational (nand2_gate ([true], [true])) = [false].
Proof. reflexivity. Qed.

(* Test bench tables for generated SystemVerilog simulation test bench *)
Definition nand_tb_inputs : list (bool * bool) :=
 [(false, false); (false, true); (true, false); (true, true)].

(* Compute expected outputs. *)
Definition nand_tb_expected_outputs : list bool :=
  map (fun '(i0,i1) => List.hd false (combinational (nand2_gate ([i0], [i1])%list))) nand_tb_inputs.

Definition nand2_tb :=
  testBench "nand2_tb" nand2Interface nand_tb_inputs nand_tb_expected_outputs.
