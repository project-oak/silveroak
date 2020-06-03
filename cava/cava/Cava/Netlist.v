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

Inductive SignalEdge :=
| PositiveEdge
| NegativeEdge.

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
  | IndexAlt: forall sz szs,
      @denoteBitVecWith nat Signal (sz::szs) ->
      list Signal ->
      @denoteBitVecWith nat Signal szs
      -> Instance
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
  clkName        : string;
  clkEdge        : SignalEdge;
  rstName        : string;
  rstEdge        : SignalEdge;
  circuitInputs  : @shape (string * Kind);
  circuitOutputs : @shape (string * Kind);
  attributes : list CircuitAttribute;
}.

Definition mkCombinationalInterface circuitName circuitInputs circuitOutputs
                                    attributes :=
  mkCircuitInterface circuitName "" PositiveEdge
                                 "" PositiveEdge
                                 circuitInputs circuitOutputs attributes.

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
  clockNet : Signal;
  clockEdge: SignalEdge;
  resetNet : Signal;
  resetEdge : SignalEdge;
  module : Module;
}.

Definition newWire : state CavaState Signal :=
  cs <- get;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge m
      => put (mkCavaState (o+1) clk clkEdge rst rstEdge m) ;;
         ret (Wire o)
  end.

Definition newWires (width : nat) : state CavaState (list Signal) :=
  cs <- get ;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge m =>
      let outv := map N.of_nat (seq (N.to_nat o) width) in
      put (mkCavaState (o + N.of_nat width) clk clkEdge rst rstEdge m) ;;
      ret (map Wire outv)
  end.

Definition newWiresBitVec (sizes: list nat) : state CavaState (@denoteBitVecWith nat Signal sizes) :=
  cs <- get ;;
  let wireCount := (bitsInPortShape (One (BitVec sizes)))%N in
  let bv := numberBitVec 0 sizes sizes in
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge m =>
      put (mkCavaState (o + N.of_nat wireCount) clk clkEdge rst rstEdge m) ;;
      ret bv
  end.

Fixpoint newWiresFromShape (s: bundle) : state CavaState (signalTy Signal s) :=
  match s with
  | Empty => ret tt
  | One Bit => newWire
  | One (BitVec s) => newWiresBitVec s
  | Tuple2 x y =>
    x <- newWiresFromShape x;;
    y <- newWiresFromShape y;;
    ret (x,y)
  end.

Definition addInstance (newInst: Instance) : state CavaState unit :=
  cs <- get;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge (mkModule name insts inputs outputs)
    => put (mkCavaState o clk clkEdge rst rstEdge (mkModule name (newInst::insts) inputs outputs))
  end.

Fixpoint addInstances (insts: list Instance) : state CavaState unit :=
  match insts with
  | [] => ret tt
  | x :: xs =>
    addInstance x ;; 
    addInstances xs
  end.

Definition addSequentialInstance (newInst: Instance) : state CavaState unit :=
  cs <- get;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge (mkModule name insts inputs outputs)
    => put (mkCavaState o clk clkEdge rst rstEdge (mkModule name (newInst::insts) inputs outputs))
  end.

Fixpoint addSequentialInstances (insts: list Instance) : state CavaState unit :=
  match insts with
  | [] => ret tt
  | x :: xs =>
    addSequentialInstance x ;; 
    addSequentialInstances xs
  end.

Definition addInputPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match newPort with
  | mkPort "" _ => ret tt (* Clock or reset not used *)
  | _ => match cs with
         | mkCavaState o clk clkEdge rst rstEdge (mkModule n insts inputs outputs) =>
           put (mkCavaState o clk clkEdge rst rstEdge (mkModule n insts (cons newPort inputs) outputs))
         end
  end.

Definition addOutputPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge (mkModule n insts inputs outputs) =>
      put (mkCavaState o clk clkEdge rst rstEdge (mkModule n insts inputs (cons newPort outputs)))
  end.

(******************************************************************************)
(* Define netlist functions used to specify top-level module behaviour.       *)
(******************************************************************************)

Definition setModuleName (name : string) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge (mkModule _ insts inputs outputs)
     => put (mkCavaState o clk clkEdge rst rstEdge (mkModule name insts inputs outputs))
  end.

Definition setClockAndReset (clk_and_edge: Signal * SignalEdge)
                            (rst_and_edge: Signal * SignalEdge)
                            : state CavaState unit :=
  let (clk, clkEdge) := clk_and_edge in
  let (rst, rstEdge) := rst_and_edge in
  cs <- get ;;
  match cs with
  | mkCavaState o _ _ _ _ m
     => put (mkCavaState o clk clkEdge rst rstEdge m)
  end.

Definition getClockAndReset : state CavaState ((Signal * SignalEdge) *
                                               (Signal * SignalEdge)) :=
  cs <- get ;;
  match cs with
  | mkCavaState _ clk clkEdge rst rstEdge _ =>
     ret ((clk, clkEdge), (rst, rstEdge))
  end.                                       

Definition inputBit (name : string) : state CavaState Signal :=
  addInputPort (mkPort name Bit) ;;
  ret (NamedWire name).

Definition inputVectorTo0 (sizes : list nat) (name : string) : state CavaState (@denoteBitVecWith nat Signal sizes) :=
  cs <- get ;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge (mkModule n insts inputs outputs)
     => let newPort := mkPort name (BitVec sizes) in
        addInputPort newPort ;;
        ret (smashBitVec name sizes sizes [])
  end.

Definition outputBit (name : string) (i : Signal) : state CavaState Signal :=
  cs <- get ;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge (mkModule n insts inputs outputs)
     => let newPort := mkPort name Bit in
        let insts' := WireOutputBit name i :: insts in
        put (mkCavaState o clk clkEdge rst rstEdge (mkModule n insts' inputs (newPort :: outputs))) ;;
        ret i
  end.

Definition outputVectorTo0 (sizes : list nat) (v : @denoteBitVecWith nat Signal sizes) (name : string) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o clk clkEdge rst rstEdge (mkModule n insts inputs outputs)
     => let newPort := mkPort name (BitVec sizes) in
        let insts' := WireOutputBitVec sizes name v :: insts in
        put (mkCavaState o clk clkEdge rst rstEdge (mkModule n insts' inputs (newPort :: outputs))) ;;
        ret tt
  end.

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

(* Net number 0 carries the constant signal zero. Net number 1 carries the
   constant signal 1. We start numbering from 2 for the user nets.
*)

Definition initStateFrom (startAt : N) : CavaState
  := mkCavaState startAt UndefinedSignal PositiveEdge UndefinedSignal PositiveEdge
                 (mkModule "noname" [] [] []).

Definition initState : CavaState
  := initStateFrom 0.

(******************************************************************************)
(* Execute a monadic circuit description and return the generated netlist.    *)
(******************************************************************************)

Fixpoint instantiateInputPorts (inputs: @shape (string * Kind)) : state CavaState (signalTy Signal (mapShape snd inputs)) :=
  match inputs return state CavaState (signalTy Signal (mapShape snd inputs)) with
  | Empty => ret tt
  | One (name, typ) =>
      match typ return state CavaState (signalTy Signal (mapShape snd (One (name, typ)))) with
      | Bit => i <- inputBit name ;;
               ret i
      | BitVec xs => i <- inputVectorTo0 xs name ;;
                     ret i
      end
  | Tuple2 t1 t2 => a <- instantiateInputPorts t1 ;;
                    b <- instantiateInputPorts t2 ;;
                    ret (a, b)
  end.

Definition instantiateOutputPort (pd_driver : string * Kind * Signal)
                                 : state CavaState unit :=
  match pd_driver with
  | (name, Bit, s) => _ <- outputBit name s ;; ret tt
  | (name, BitVec [n], Vec s) => _ <- outputVectorTo0 [n] s name ;; ret tt
  | _ => ret tt
  end.

Definition wireUpCircuit (intf : CircuitInterface)
                         `{ToSignal (signalTy Signal (mapShape snd (circuitOutputs intf)))}
                         (circuit : (signalTy Signal (mapShape snd (circuitInputs intf))) ->
                                    state CavaState (signalTy Signal (mapShape snd (circuitOutputs intf))))

                         : state CavaState unit  :=
  setModuleName (circuitName intf) ;;
  setClockAndReset (NamedWire (clkName intf), clkEdge intf) (NamedWire (rstName intf), rstEdge intf) ;;
  addInputPort (mkPort (clkName intf) Bit) ;;
  addInputPort (mkPort (rstName intf) Bit) ;;
  i <- instantiateInputPorts (circuitInputs intf) ;;
  o <- circuit i ;;
  mapShapeM_ instantiateOutputPort (zipShapes (circuitOutputs intf) (toSignal o)).

Definition makeNetlist (intf : CircuitInterface)
                       `{ToSignal (signalTy Signal (mapShape snd (circuitOutputs intf)))}
                       (circuit : signalTy Signal (mapShape snd (circuitInputs intf)) ->
                                  state CavaState (signalTy Signal (mapShape snd (circuitOutputs intf)))) : CavaState
  := execState (wireUpCircuit intf circuit) initState.

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
