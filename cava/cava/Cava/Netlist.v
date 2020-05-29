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
Require Export ExtLib.Data.Monads.StateMonad.

Require Import Omega.

Import ListNotations.
Import MonadNotation.
Open Scope list_scope.
Open Scope monad_scope.

From Cava Require Import Signal.
From Cava Require Import Types.

(******************************************************************************)
(* Make it possible to convert certain types to bool shape values             *)
(******************************************************************************)

Inductive SignalExpr :=
| NoSignal : SignalExpr
| BitVal : bool -> SignalExpr
| VecVal : list SignalExpr -> SignalExpr.

Class ToSignalExpr t := {
  toSignalExpr : t -> @shape SignalExpr;
}.

Instance SignalBool : ToSignalExpr bool := {
  toSignalExpr b := One (BitVal b);
}.

Fixpoint shapeToSignalExpr (s : @shape SignalExpr) : SignalExpr :=
  match s with
  | One v => v
  | _ => NoSignal
  end.

Instance ShapeVec {A : Type} `{ToSignalExpr A} : ToSignalExpr (list A) := {
   toSignalExpr v := One (VecVal (map (compose shapeToSignalExpr toSignalExpr) v)) ;
}.

Instance ToShapePair {A B : Type} `{ToSignalExpr A} `{ToSignalExpr B}  :
                     ToSignalExpr (A * B) := {
  toSignalExpr '(a, b) := Tuple2 (toSignalExpr a) (toSignalExpr b);
}.

(* Likewise for Signal *)

Class ToSignal t := {
  toSignal: t -> @shape Signal;
}.

Instance SignalWire : ToSignal Signal := {
  toSignal s := One s;
}.

Fixpoint shapeToSignalValue (s : @shape Signal) : Signal :=
  match s with
  | One v => v
  | _ => Vcc
  end.

Instance ShapeSignalVec {A : Type} `{ToSignal A} : ToSignal (list A) := {
   toSignal v := One (Vec (map (compose shapeToSignalValue toSignal) v)) ;
}.

Instance ToShapePairSignal {A B : Type} `{ToSignal A} `{ToSignal B}  :
                     ToSignal (A * B) := {
  toSignal '(a, b) := Tuple2 (toSignal a) (toSignal b);
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
  | WireInputBit:     string -> Signal -> Instance
  | WireInputBitVec:  forall sizes, string ->
                      @denoteBitVecWith nat Signal sizes -> Instance
  | WireOutputBit:    string -> Signal -> Instance
  | WireOutputBitVec: forall sizes, string ->
                      @denoteBitVecWith nat Signal sizes -> Instance
  (* SystemVerilog primitive gates. *)
  | Not:       Signal -> Signal -> Instance
  | And:       Signal -> Signal -> Signal -> Instance
  | Nand:      Signal -> Signal -> Signal -> Instance
  | Or:        Signal -> Signal -> Signal -> Instance
  | Nor:       Signal -> Signal -> Signal -> Instance
  | Xor:       Signal -> Signal -> Signal -> Instance
  | Xnor:      Signal -> Signal -> Signal -> Instance
  | Buf:       Signal -> Signal -> Instance
  (* A Cava unit delay bit component. *)
  | DelayBit:  Signal -> Signal -> Instance
  (* Assignment of bit wire *)
  | AssignBit: Signal -> Signal -> Instance
  (* Arithmetic operations *)
  | UnsignedAdd : list Signal -> list Signal -> list Signal -> Instance
  (* Multiplexors *)    
  | IndexBitArray: list Signal -> list Signal -> Signal -> Instance
  | IndexArray: list (list Signal) -> list Signal -> list Signal -> Instance
  | Component: string -> list (string * ConstExpr) -> list (string * Signal) ->
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

Record CavaState : Type := mkCavaState {
  netNumber : N;
  isSequential : bool;
  module : Module;
}.

Definition newWire : state CavaState Signal :=
  cs <- get;;
  match cs with
  | mkCavaState o isSeq m
      => put (mkCavaState (o+1) isSeq m) ;;
         ret (Wire o)
  end.

Definition newWires (width : nat) : state CavaState (list Signal) :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq m =>
      let outv := map N.of_nat (seq (N.to_nat o) width) in
      put (mkCavaState (o + N.of_nat width) isSeq m) ;;
      ret (map Wire outv)
  end.

Definition addInstance (newInst: Instance) : state CavaState unit :=
  cs <- get;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
    => put (mkCavaState o isSeq (mkModule name (newInst::insts) inputs outputs))
  end.

Definition addSequentialInstance (newInst: Instance) : state CavaState unit :=
  cs <- get;;
  match cs with
  | mkCavaState o _ (mkModule name insts inputs outputs)
    => put (mkCavaState o true (mkModule name (newInst::insts) inputs outputs))
  end.

Definition addPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs) =>
      put (mkCavaState o isSeq (mkModule n insts (cons newPort inputs) outputs))
  end.

Record TestBench : Type := mkTestBench {
  testBenchName            : string;
  testBenchInterface       : CircuitInterface;
  testBenchInputs          : list (list SignalExpr);
  testBenchExpectedOutputs : list (list SignalExpr);
}.

Definition testBench (name : string)
                     (intf : CircuitInterface)
                     `{ToSignalExpr (signalTy bool (mapShape snd (circuitInputs intf)))}
                     `{ToSignalExpr (signalTy bool (mapShape snd (circuitOutputs intf)))}
                     (testInputs : list (signalTy bool (mapShape snd (circuitInputs intf))))
                     (testExpectedOutputs : list (signalTy bool (mapShape snd (circuitOutputs intf))))
  := mkTestBench name intf (map (compose flattenShape toSignalExpr) testInputs)
                           (map (compose flattenShape toSignalExpr) testExpectedOutputs).

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

(* Net number 0 carries the constant signal zero. Net number 1 carries the
   constant signal 1. We start numbering from 2 for the user nets.
*)

Definition initStateFrom (startAt : N) : CavaState
  := mkCavaState startAt false (mkModule "noname" [] [] []).

Definition initState : CavaState
  := initStateFrom 0.
