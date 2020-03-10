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
   Coq for the specification, implementaiton and formal verification of circuits.
   Experimental work, very much in flux, as Satnam learns Coq!
*)

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
Import ListNotations.

(******************************************************************************)
(* Primitive elements                                                         *)
(******************************************************************************)

(* The primitive elements that can be instantiated in Cava. Some are generic
   SystemVerilog gates that can be used with synthesis and back-end tools to
   map to any architecture, while others are specific to Xilinx FPGAs.
*)

Inductive Primitive :=
  (* SystemVerilog primitive gates. *)
  | Not  : Z -> Z -> Primitive
  | And  : list Z -> Z -> Primitive
  | Nand : list Z -> Z -> Primitive
  | Or   : list Z -> Z -> Primitive
  | Nor  : list Z -> Z -> Primitive
  | Xor  : list Z -> Z -> Primitive
  | Xnor : list Z -> Z -> Primitive
  | Buf  : Z -> Z -> Primitive
  (* A Cava unit delay bit component. *)
  | DelayBit : Z -> Z -> Primitive
  (* Assignment of bit wire *)
  | AssignBit : Z -> Z -> Primitive
  (* Xilinx FPGA architecture specific gates. *)
  | Xorcy : Z -> Z -> Z -> Primitive
  | Muxcy : Z -> Z -> Z -> Z -> Primitive.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Inductive PortType :=
  | BitPort : Z -> PortType
  | VectorTo0Port : list Z -> PortType
  | VectorFrom0Port : list Z -> PortType.

Record PortDeclaration : Type := mkPort {
  port_name : string;
  port_type : PortType;
}.

Notation Netlist := (list Primitive).

Record Module : Type := mkModule {
  moduleName : string;
  netlist : Netlist;
  inputs : list PortDeclaration;
  outputs : list PortDeclaration;
}.

Record CavaState : Type := mkCavaState {
  netNumber : Z;
  isSequential : bool;
  module : Module;
}.

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

(* Net number 0 carries the constant signal zero. Net number 1 carries the
   constant signal 1. We start numbering from 2 for the user nets.
*)

Definition initStateFrom (startAt : Z) : CavaState
  := mkCavaState startAt false (mkModule "" [] [] []).

Definition initState : CavaState
  := initStateFrom 2.
