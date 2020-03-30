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
   Coq for the specification, implementaiton and formal verification of circuits.
   Experimental work, very much in flux, as Satnam learns Coq!
*)

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
From Coq Require Import Vector.
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
  | Not  : N -> N -> Primitive
  | And  : list N -> N -> Primitive
  | Nand : list N -> N -> Primitive
  | Or   : list N -> N -> Primitive
  | Nor  : list N -> N -> Primitive
  | Xor  : list N -> N -> Primitive
  | Xnor : list N -> N -> Primitive
  | Buf  : N -> N -> Primitive
  (* A Cava unit delay bit component. *)
  | DelayBit : N -> N -> Primitive
  (* Assignment of bit wire *)
  | AssignBit : N -> N -> Primitive
  (* Arithmetic operations *)
  | UnsignedAdd : forall m n, Vector.t N m -> Vector.t N n ->
                              Vector.t N (max m n + 1) -> Primitive
  (* Xilinx FPGA architecture specific gates. *)
  | Xorcy : N -> N -> N -> Primitive
  | Muxcy : N -> N -> N -> N -> Primitive.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Inductive PortType :=
  | BitPort : N -> PortType
  | VectorTo0Port : forall n, Vector.t N n -> PortType
  | VectorFrom0Port : forall n, Vector.t N n  -> PortType.

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
  netNumber : N;
  isSequential : bool;
  module : Module;
}.

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

(* Net number 0 carries the constant signal zero. Net number 1 carries the
   constant signal 1. We start numbering from 2 for the user nets.
*)

Definition initStateFrom (startAt : N) : CavaState
  := mkCavaState startAt false (mkModule "" [] [] []).

Definition initState : CavaState
  := initStateFrom 2.
