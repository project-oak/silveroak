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
From Coq Require Import Ascii String.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Numbers.NaryFunctions.
From Coq Require Import Init.Datatypes.
Require Import ExtLib.Structures.Monads.

Require Import Omega.

Import ListNotations.
Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.

From Cava Require Import Types.

(******************************************************************************)
(* Make it possible to convert ceratain types to bool shape values            *)
(******************************************************************************)

Inductive Signal :=
| NoSignal : Signal
| BitVal : bool -> Signal
| VecVal : list Signal -> Signal.

Class ToShape t := {
  shapeIt : t -> @shape Signal;
}.

Instance SignalBool : ToShape bool := {
  shapeIt b := One (BitVal b);
}.

Fixpoint shapeToSignal (s : shape) : Signal :=
  match s with
  | One v => v
  | _ => NoSignal
  end.

Instance ShapeVec {A : Type} `{ToShape A} : ToShape (list A) := {
  shapeIt v := One (VecVal (map (compose shapeToSignal shapeIt) v)) ;
}.

Instance ToShapePair {A B : Type} `{ToShape A} `{ToShape B}  :
                     ToShape (A * B) := {
  shapeIt '(a, b) := Tuple2 (shapeIt a) (shapeIt b);
}.

(******************************************************************************)
(* Flatten allows us to extract values from a result produced from a toplevel *)
(* Cava circuit, which must produce a result that is an instance of the       *)
(* the Flatten class.                                                         *)
(******************************************************************************)

Class Flatten t := {
  flatten : t -> list N;
}.

Instance FlattenN : Flatten N := {
  flatten n := [n];
}.

Instance FlattenTuple2 {a b} `{Flatten a} `{Flatten b}  : Flatten (a * b) := {
  flatten ab := match ab with
                | (a, b) => flatten a ++ flatten b
                end;
}.

Instance FlattenList {a} `{Flatten a} : Flatten (list a) := {
  flatten l := concat (map flatten l);
}.

(******************************************************************************)
(* PrimitiveInstance elements                                                 *)
(******************************************************************************)

(* The primitive elements that can be instantiated in Cava. These are generic
   SystemVerilog gates that can be used with synthesis and back-end tools to
   map to any architecture.
*)

Inductive ConstExpr : Type :=
| HexLiteral: nat -> N -> ConstExpr
| StringLiteral: string -> ConstExpr.

Inductive Instance : Type :=
  (* I/O port wiring *)
  | WireInputBit:     string -> N -> Instance
  | WireInputBitVec:  forall sizes, string ->
                      @denoteBitVecWith nat N sizes -> Instance
  | WireOutputBit:    string -> N -> Instance
  | WireOutputBitVec: forall sizes, string ->
                      @denoteBitVecWith nat N sizes -> Instance
  (* SystemVerilog primitive gates. *)
  | Not:       N -> N -> Instance
  | And:       N -> N -> N -> Instance
  | Nand:      N -> N -> N -> Instance
  | Or:        N -> N -> N -> Instance
  | Nor:       N -> N -> N -> Instance
  | Xor:       N -> N -> N -> Instance
  | Xnor:      N -> N -> N -> Instance
  | Buf:       N -> N -> Instance
  (* A Cava unit delay bit component. *)
  | DelayBit:  N -> N -> Instance
  (* Assignment of bit wire *)
  | AssignBit: N -> N -> Instance
  (* Arithmetic operations *)
  | UnsignedAdd : list N -> list N -> list N -> Instance
  (* Multiplexors *)    
  | IndexBitArray: list N -> list N -> N -> Instance
  | IndexArray: list (list N) -> list N -> list N -> Instance
  | Component: string -> list (string * ConstExpr) -> list (string * N) ->
               Instance.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Record PortDeclaration : Type := mkPort {
  port_name : string;
  port_shape : Kind;
}.

Notation Netlist := (list Instance).

Record Module : Type := mkModule {
  moduleName : string;
  netlist : Netlist;
  inputs :  list PortDeclaration;
  outputs : list PortDeclaration;
}.

Inductive CircuitAttribute :=
  | ClockName : string -> CircuitAttribute
  | ResetName : string -> CircuitAttribute.

Record CircuitInterface : Type := mkCircuitInterface {
  circuitName    : string;
  circuitInputs  : @shape (string * Kind);
  circuitOutputs : @shape (string * Kind);
  attributes : list CircuitAttribute;
}.

Fixpoint shapeToPortDeclaration (s : @shape (string * Kind)) :
                                list PortDeclaration :=
  match s with
  | Empty => []
  | One thing => match thing with
                 | (name, Bit) => [mkPort name Bit]
                 | (name, BitVec ns) => [mkPort name (BitVec ns)]
                 end
  | Tuple2 t1 t2 => shapeToPortDeclaration t1 ++ shapeToPortDeclaration t2
  end.

Definition circuitInterfaceToModule (ci : CircuitInterface)
                                    (nl : Netlist) : Module :=
  mkModule (circuitName  ci) nl (shapeToPortDeclaration (circuitInputs ci))
                                (shapeToPortDeclaration (circuitOutputs ci)).

Record CavaState : Type := mkCavaState {
  netNumber : N;
  isSequential : bool;
  module : Module;
}.

Record TestBench : Type := mkTestBench {
  testBenchName            : string;
  testBenchInterface       : CircuitInterface;
  testBenchInputs          : list (list Signal);
  testBenchExpectedOutputs : list (list Signal);
}.

Definition testBench (name : string)
                     (intf : CircuitInterface)
                     `{ToShape (signalTy bool (mapShape snd (circuitInputs intf)))}
                     `{ToShape (signalTy bool (mapShape snd (circuitOutputs intf)))}
                     (testInputs : list (signalTy bool (mapShape snd (circuitInputs intf))))
                     (testExpectedOutputs : list (signalTy bool (mapShape snd (circuitOutputs intf))))
  := mkTestBench name intf (map (compose flattenShape shapeIt) testInputs)
                           (map (compose flattenShape shapeIt) testExpectedOutputs).

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

(* Net number 0 carries the constant signal zero. Net number 1 carries the
   constant signal 1. We start numbering from 2 for the user nets.
*)

Definition initStateFrom (startAt : N) : CavaState
  := mkCavaState startAt false (mkModule "noname" [] [] []).

Definition initState : CavaState
  := initStateFrom 2.
