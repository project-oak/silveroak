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
From Coq Require Vector.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.StateMonad.
Require Export ExtLib.Data.List.
From ExtLib Require Import Structures.Traversable.

Require Import Omega.

Import ListNotations.
Import MonadNotation.
Open Scope string_scope.
Open Scope list_scope.
Open Scope monad_scope.

From Cava Require Import Kind.
From Cava Require Import Signal.
From Cava Require Import Types.
From Cava Require Import BitArithmetic.
From Cava Require Import VectorUtils.

(******************************************************************************)
(* Make it possible to convert certain types to bool shape values             *)
(******************************************************************************)

Inductive SignalExpr :=
| NoSignal : SignalExpr
| BitVal : bool -> SignalExpr
| VecVal : list SignalExpr -> SignalExpr.

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

(* The function takes a Kind and returns the smashed default value for
   that Kind.
*)
Fixpoint defaultKind (k: Kind) : smashNetTy k :=
  match k return smashNetTy k with
  | Void => UndefinedSignal
  | Bit => Gnd
  | BitVec k2 s => Vector.const (defaultKind k2) s
  | ExternalType _ => UninterpretedSignal "XXX"
  end.

Inductive Instance : Type :=
  (* SystemVerilog primitive gates. *)
  | Not:       Signal Bit -> Signal Bit -> Instance
  | And:       Signal Bit -> Signal Bit -> Signal Bit -> Instance
  | Nand:      Signal Bit -> Signal Bit -> Signal Bit -> Instance
  | Or:        Signal Bit -> Signal Bit -> Signal Bit -> Instance
  | Nor:       Signal Bit -> Signal Bit -> Signal Bit -> Instance
  | Xor:       Signal Bit -> Signal Bit -> Signal Bit -> Instance
  | Xnor:      Signal Bit -> Signal Bit -> Signal Bit -> Instance
  | Buf:       Signal Bit -> Signal Bit -> Instance
  (* A Cava unit delay bit component. *)
  | DelayBit:  Signal Bit -> Signal Bit -> Instance
  (* Assignment of bit wire *)
  | AssignSignal: forall {k: Kind}, Signal k -> Signal k -> Instance
  (* Arithmetic operations *)
  | UnsignedAdd : forall {a b c : nat}, Signal (BitVec Bit a) ->
                                        Signal (BitVec Bit b) ->
                                        Signal (BitVec Bit c) ->
                                        Instance
  (* Relational operations *)
  | GreaterThanOrEqual: forall {a b : nat}, Signal (BitVec Bit a) ->
                                            Signal (BitVec Bit b) ->
                                            Signal Bit ->
                                            Instance
  | Component: string ->
               list (string * ConstExpr) ->
               list (string * UntypedSignal) ->
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
  circuitInputs  : @shape PortDeclaration;
  circuitOutputs : @shape PortDeclaration;
  attributes : list CircuitAttribute;
}.

Definition sequentialInterface {ciType coType}
                              `{@ToShape PortDeclaration ciType}
                              `{@ToShape PortDeclaration coType}
                               (circuitName: string)
                               (clkName: string) (clkEdge: SignalEdge)
                               (rstName: string) (rstEdge: SignalEdge)
                               (circuitInputs: ciType) 
                               (circuitOutputs: coType)
                               (attributes: list CircuitAttribute) :=
  mkCircuitInterface circuitName clkName clkEdge rstName rstEdge
                     (toShape circuitInputs) (toShape circuitOutputs) attributes.                            

Definition combinationalInterface {ciType coType}
                                  `{@ToShape PortDeclaration ciType}
                                  `{@ToShape PortDeclaration coType}
                                  (circuitName: string)
                                  (circuitInputs: ciType) 
                                  (circuitOutputs: coType)
                                  (attributes: list CircuitAttribute) :=
  sequentialInterface circuitName "" PositiveEdge
                                  "" PositiveEdge
                                  circuitInputs circuitOutputs attributes.

Record CavaState : Type := mkCavaState {
  netNumber : N;
  vectorNumber : N;
  vectorDeclarations : list (Kind * nat);
  clockNet : option (Signal Bit);
  clockEdge: SignalEdge;
  resetNet : option (Signal Bit);
  resetEdge : SignalEdge;
  module : Module;
}.


(* Used in the Haskell back end *)
Definition incN (n: N) : N := n + 1.

Definition newWire : state CavaState (Signal Bit) :=
  cs <- get;;
  match cs with
  | mkCavaState o vCount vDefs clk clkEdge rst rstEdge m
      => put (mkCavaState (o+1) vCount vDefs clk clkEdge rst rstEdge m) ;;
         ret (Wire o)
  end.

Definition newWires (width : nat) : state CavaState (list (Signal Bit)) :=
  cs <- get ;;
  match cs with
  | mkCavaState o vCount vDefs clk clkEdge rst rstEdge m =>
      let outv := map N.of_nat (seq (N.to_nat o) width) in
      put (mkCavaState (o + N.of_nat width) vCount vDefs clk clkEdge rst rstEdge m) ;;
      ret (map Wire outv)
  end.

Definition newVector (k : Kind) (s: nat) : state CavaState (Signal (BitVec k s)) :=
  cs <- get ;;
  match cs with
  | mkCavaState o vCount vDefs clk clkEdge rst rstEdge m =>
      put (mkCavaState o (vCount + 1) (vDefs ++ [(k, s)]) clk clkEdge rst rstEdge m) ;;
      ret (LocalBitVec k s vCount)
  end.

Definition addInstance (newInst: Instance) : state CavaState unit :=
  cs <- get;;
  match cs with
  | mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule name insts inputs outputs)
    => put (mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule name (newInst::insts) inputs outputs))
  end.

Fixpoint addInstances (insts: list Instance) : state CavaState unit :=
  match insts with
  | [] => ret tt
  | x :: xs =>
    addInstance x ;; 
    addInstances xs
  end.

Definition getInstances : state CavaState (list Instance) :=
cs <- get;;
  match cs with
  | mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule name insts inputs outputs)
    => ret insts
  end.

Definition setInstances (insts: list Instance) : state CavaState unit :=
cs <- get;;
  match cs with
  | mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule name _ inputs outputs)
    => put (mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule name insts inputs outputs))
  end.

Definition assignSignal {k} (s1: Signal k) (s2: Signal k) :=
  addInstance (AssignSignal s1 s2).

Definition assignSmashedSignal {k: Kind} (s1: Signal k) (s2: smashTy (Signal Bit) k) :=
  addInstance (AssignSignal s1 (vecLitS s2)).

Definition addInputPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match newPort with
  | mkPort "" _ => ret tt (* Clock or reset not used *)
  | _ => match cs with
         | mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule n insts inputs outputs) =>
           put (mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule n insts (cons newPort inputs) outputs))
         end
  end.

Definition addOutputPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule n insts inputs outputs) =>
      put (mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule n insts inputs (cons newPort outputs)))
  end.

(******************************************************************************)
(* Define netlist functions used to specify top-level module behaviour.       *)
(******************************************************************************)

Definition setModuleName (name : string) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule _ insts inputs outputs)
     => put (mkCavaState o vecCount vecDefs clk clkEdge rst rstEdge (mkModule name insts inputs outputs))
  end.

Definition setClockAndReset (clk_and_edge: Signal Bit * SignalEdge)
                            (rst_and_edge: Signal Bit* SignalEdge)
                            : state CavaState unit :=
  let (clk, clkEdge) := clk_and_edge in
  let (rst, rstEdge) := rst_and_edge in
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs _ _ _ _ m
     => put (mkCavaState o vecCount vecDefs (Some clk) clkEdge (Some rst) rstEdge m)
  end.

Definition getClockAndReset : state CavaState ((option (Signal Bit) * SignalEdge) *
                                               (option (Signal Bit) * SignalEdge)) :=
  cs <- get ;;
  match cs with
  | mkCavaState _ vecCount vecDefs clk clkEdge rst rstEdge _ =>
     ret ((clk, clkEdge), (rst, rstEdge))
  end.                                       

Definition inputBit (name : string) : state CavaState (Signal Bit) :=
  addInputPort (mkPort name Bit) ;;
  ret (NamedWire name).

Definition inputVector (k: Kind) (sz: nat) (name : string) : state CavaState (smashTy (Signal Bit) (BitVec k sz)) :=
  addInputPort (mkPort name (BitVec k sz)) ;;
  ret (smash (NamedVector k sz name)).

Definition outputBit (name : string) (i : Signal Bit) : state CavaState unit :=
  addOutputPort (mkPort name Bit) ;;
  assignSignal (NamedWire name) i.

Definition outputVector (k: Kind) (sz : nat) (name : string) (v : smashTy (Signal Bit) (BitVec k sz)) : state CavaState unit :=
  addOutputPort (mkPort name (BitVec k sz)) ;;
  assignSmashedSignal (NamedVector k sz name) v.

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

Definition initStateFrom (startAt : N) : CavaState
  := mkCavaState startAt 0 [] None PositiveEdge None PositiveEdge
                 (mkModule "noname" [] [] []).

Definition initState : CavaState
  := initStateFrom 0.
  
(******************************************************************************)
(* Execute a monadic circuit description and return the generated netlist.    *)
(******************************************************************************)
      
Fixpoint instantiateInputPorts (inputs: @shape PortDeclaration) : state CavaState (signalSmashTy (mapShape port_shape inputs)) :=
  match inputs return state CavaState (signalSmashTy (mapShape port_shape inputs)) with
  | Empty => ret tt
  | One (mkPort name typ) =>
      match typ with
      | Void => ret UndefinedSignal
      | Bit => inputBit name
      | BitVec k sz => inputVector k sz name
      | ExternalType t => addInputPort (mkPort name (ExternalType t)) ;;
                          ret (UninterpretedSignal t)
      end
  | Tuple2 t1 t2 => a <- instantiateInputPorts t1 ;;
                    b <- instantiateInputPorts t2 ;;
                    ret (a, b)
  end.

Fixpoint instantiateOutputPorts (outputs: @shape PortDeclaration) (v: signalSmashTy (mapShape port_shape outputs)) : state CavaState unit :=
  match outputs, v with
  | Empty, _ => ret tt
  | One (mkPort name typ), _ =>
     match typ, v  with
     | Void, _ => ret tt
     | Bit, s => outputBit name s
     | BitVec k sz, s => outputVector k sz name s
     | ExternalType t, s => addOutputPort (mkPort name (ExternalType t)) ;;
                            assignSignal (UninterpretedSignal name) s
     end
  | Tuple2 t1 t2, (a, b) => instantiateOutputPorts t1 a ;;
                            instantiateOutputPorts t2 b
  end.

Definition wireUpCircuit (intf : CircuitInterface)
                         (circuit : (signalSmashTy (mapShape port_shape (circuitInputs intf))) ->
                                    state CavaState (signalSmashTy (mapShape port_shape (circuitOutputs intf))))

                         : state CavaState unit  :=
  setModuleName (circuitName intf) ;;
  setClockAndReset (NamedWire (clkName intf), clkEdge intf) (NamedWire (rstName intf), rstEdge intf) ;;
  addInputPort (mkPort (clkName intf) Bit) ;;
  addInputPort (mkPort (rstName intf) Bit) ;;
  i <- instantiateInputPorts (circuitInputs intf) ;;
  o <- circuit i ;;
  let outType := circuitOutputs intf in 
  instantiateOutputPorts outType o.

Definition makeNetlist (intf : CircuitInterface)                      
                       (circuit : signalSmashTy (mapShape port_shape (circuitInputs intf)) ->
                                  state CavaState (signalSmashTy (mapShape port_shape (circuitOutputs intf)))) : CavaState
  := execState (wireUpCircuit intf circuit) initState.

Record TestBench : Type := mkTestBench {
  testBenchName            : string;
  testBenchInterface       : CircuitInterface;
  testBenchInputs          : list (list SignalExpr);
  testBenchExpectedOutputs : list (list SignalExpr);
}.

Fixpoint vec2expr {k sz} (v: signalTy bool (One (BitVec k sz))) : SignalExpr :=
  match k, v with
  | Void, _ => NoSignal
  | Bit, zx => VecVal (map BitVal (Vector.to_list zx))
  | BitVec k s2, y => VecVal (map (@vec2expr k s2) (Vector.to_list y))
  | ExternalType t, zx => NoSignal
  end.

Fixpoint denoteValueWithSignalExpr (t: @shape Kind) (v: signalTy bool t) : @shape SignalExpr :=
  match t, v with
  | Empty, _ => Empty
  | One Void, x => One NoSignal
  | One Bit, x => One (BitVal x)
  | One (BitVec k sz), xs => One (vec2expr xs)
  | One (ExternalType _), _ => One NoSignal
  | Tuple2 t1 t2, (a, b) => Tuple2 (denoteValueWithSignalExpr t1 a) (denoteValueWithSignalExpr t2 b)
  end.

Definition testBench (name : string)
                     (intf : CircuitInterface)
                     (testInputs : list (signalTy bool (mapShape port_shape (circuitInputs intf))))
                     (testExpectedOutputs : list (signalTy bool (mapShape port_shape (circuitOutputs intf))))
  := let inShape  : @shape Kind := mapShape port_shape (circuitInputs intf) in
     let outShape : @shape Kind := mapShape port_shape (circuitOutputs intf) in
     mkTestBench name intf (map (compose flattenShape (denoteValueWithSignalExpr inShape)) testInputs)
                           (map (compose flattenShape (denoteValueWithSignalExpr outShape)) testExpectedOutputs).
