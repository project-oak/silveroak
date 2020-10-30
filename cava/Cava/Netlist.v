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

Require Import Coq.Program.Basics.
From Coq Require Import Strings.Ascii Strings.String.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Coq Require Import Numbers.NaryFunctions.
From Coq Require Import Init.Datatypes.
From Coq Require Vector.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.StateMonad.
Require Export ExtLib.Data.List.
From ExtLib Require Import Structures.Traversable.

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
  | AssignSignal: forall {k: SignalType}, Signal k -> Signal k -> Instance
  (* Arithmetic operations *)
  | UnsignedAdd : forall {a b c : nat}, Signal (Vec Bit a) ->
                                        Signal (Vec Bit b) ->
                                        Signal (Vec Bit c) ->
                                        Instance
  | UnsignedSubtract : forall {a b c : nat}, Signal (Vec Bit a) ->
                                        Signal (Vec Bit b) ->
                                        Signal (Vec Bit c) ->
                                        Instance
  | UnsignedMultiply : forall {a b c : nat}, Signal (Vec Bit a) ->
                                        Signal (Vec Bit b) ->
                                        Signal (Vec Bit c) ->
                                        Instance
  (* Relational operations *)
  | GreaterThanOrEqual: forall {a b : nat}, Signal (Vec Bit a) ->
                                            Signal (Vec Bit b) ->
                                            Signal Bit ->
                                            Instance
  | Component: string ->
               list (string * ConstExpr) ->
               list (string * UntypedSignal) ->
               Instance.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Notation Netlist := (list Instance).

Fixpoint denotePortNames (s : SignalType) : Type :=
  match s with
  | Pair t1 t2 => denotePortNames t1 * denotePortNames t2
  | other => string
  end.

Fixpoint denotePortDeclarations (s : SignalType) : Type :=
  match s with
  | Pair t1 t2 => denotePortDeclarations t1 * denotePortDeclarations t2
  | other => string * SignalType
  end.

Record PortDeclaration : Type := mkPort {
  port_name : string;
  port_type : SignalType;
}.

Fixpoint projectPortNames {t : SignalType} (pd : denotePortDeclarations t) :
                          denotePortNames t :=
  match t, pd with
  | Pair t1 t2, (a, b) => (projectPortNames a, projectPortNames b)
  | _, (name, _) => name
  end.

Fixpoint flattenPortDeclarations {t : SignalType}
                                 (pd : denotePortDeclarations t) :
                                 list PortDeclaration :=
  match t , pd with
  | Pair t1 t2, pv => let v1 := flattenPortDeclarations (fst pv) in
                      let v2 := flattenPortDeclarations (snd pv) in
                      v1 ++ v2
  | _, opv => [mkPort (fst opv) (snd opv)]
  end.

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
  circuitName           : string;
  clkName                : string;
  clkEdge                : SignalEdge;
  rstName                : string;
  rstEdge                : SignalEdge;
  circuitInputType       : SignalType;
  circuitInputPortNames  : denotePortNames circuitInputType;
  circuitOutputType      : SignalType;
  circuitOutputPortNames : denotePortNames circuitOutputType;
  attributes             : list CircuitAttribute;
}.

Definition sequentialInterface {ciType coType : SignalType}
                               (circuitName: string)
                               (clkName: string) (clkEdge: SignalEdge)
                               (rstName: string) (rstEdge: SignalEdge)
                               (circuitInputs: denotePortDeclarations ciType)
                               (circuitOutputs: denotePortDeclarations coType)
                               (attributes: list CircuitAttribute) :=
  mkCircuitInterface circuitName clkName clkEdge rstName rstEdge
                     ciType (projectPortNames circuitInputs)
                     coType (projectPortNames circuitOutputs)
                     attributes.

Definition combinationalInterface {ciType coType : SignalType}
                                  (circuitName: string)
                                  (circuitInputs: denotePortDeclarations ciType)
                                  (circuitOutputs: denotePortDeclarations coType)
                                  (attributes: list CircuitAttribute) :=
  sequentialInterface circuitName "" PositiveEdge
                                  "" PositiveEdge
                                  circuitInputs circuitOutputs attributes.

(******************************************************************************)
(* The CavaState data structure is what is computed bu the the netlist        *)
(* interpretation. It contains circuit wide information like the nature of    *)
(* clock and reset, auxillary data structure to help provide fresh names for  *)
(* new nets and vectors as well as all the circuit modules in the design.     *)
(******************************************************************************)

Record CavaState : Type := mkCavaState {
  netNumber : N;
  vectorNumber : N;
  vectorDeclarations : list (SignalType * nat);
  externalDeclarations : list string;
  clockNet : option (Signal Bit);
  clockEdge: SignalEdge;
  resetNet : option (Signal Bit);
  resetEdge : SignalEdge;
  module : Module; (* The top level module. *)
  libraryModules : list (CircuitInterface * Module);
                   (* Dependent modules of the root module. *)
}.

(* Only used in the Haskell back end *)
Definition incN (n: N) : N := n + 1.

Definition newWire : state CavaState (Signal Bit) :=
  cs <- get;;
  match cs with
  | mkCavaState o vCount vDefs ext clk clkEdge rst rstEdge m lm
      => put (mkCavaState (o+1) vCount vDefs ext clk clkEdge rst rstEdge m lm) ;;
         ret (Wire o)
  end.

Definition newWires (width : nat) : state CavaState (list (Signal Bit)) :=
  cs <- get ;;
  match cs with
  | mkCavaState o vCount vDefs ext clk clkEdge rst rstEdge m lm =>
      let outv := map N.of_nat (seq (N.to_nat o) width) in
      put (mkCavaState (o + N.of_nat width) vCount vDefs ext clk clkEdge rst rstEdge m lm) ;;
      ret (map Wire outv)
  end.

Definition newVector (t : SignalType) (s: nat) : state CavaState (Signal (Vec t s)) :=
  cs <- get ;;
  match cs with
  | mkCavaState o vCount vDefs ext clk clkEdge rst rstEdge m ml =>
      put (mkCavaState o (vCount + 1) (vDefs ++ [(t, s)]) ext clk clkEdge rst rstEdge m ml) ;;
      ret (LocalVec t s vCount)
  end.

Definition newExternal (t : string) : state CavaState (Signal (ExternalType t)) :=
  cs <- get ;;
  match cs with
  | mkCavaState o vCount vDefs ext clk clkEdge rst rstEdge m ml =>
    let newExt := UninterpretedSignalIndex t (N.of_nat (length ext)) in
    put (mkCavaState o vCount vDefs (ext ++ [t]) clk clkEdge rst rstEdge m ml) ;;
    ret newExt
  end.

Definition addInstance (newInst: Instance) : state CavaState unit :=
  cs <- get;;
  match cs with
  | mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule name insts inputs outputs) lm
    => put (mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule name (newInst::insts) inputs outputs) lm)
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
  | mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule name insts inputs outputs) lm
    => ret insts
  end.

Definition setInstances (insts: list Instance) : state CavaState unit :=
cs <- get;;
  match cs with
  | mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule name _ inputs outputs) lm
    => put (mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule name insts inputs outputs) lm)
  end.

Definition assignSignal {k} (s1: Signal k) (s2: Signal k) :=
  addInstance (AssignSignal s1 s2).

Definition addInputPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match newPort with
  | mkPort "" _ => ret tt (* Clock or reset not used *)
  | _ => match cs with
         | mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule n insts inputs outputs) lm =>
           put (mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule n insts (cons newPort inputs) outputs) lm)
         end
  end.

Definition addOutputPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule n insts inputs outputs) lm =>
      put (mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule n insts inputs (cons newPort outputs)) lm)
  end.

Fixpoint findModule (name : string) (libs : list (CircuitInterface * Module)) : bool :=
  match libs with
  | [] => false
  | x::xs => if circuitName (fst x)  =? name then
               true
             else
               findModule name xs
  end.

Definition addModule (intf : CircuitInterface) (newModule : Module) : state CavaState unit :=
    cs <- get ;;
    match cs with
    | mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge m lm =>
        if findModule (circuitName intf) lm then
          ret tt
        else
          put (mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge m
               (lm ++ [(intf, newModule)]))
    end.

(******************************************************************************)
(* Define netlist functions used to specify top-level module behaviour.       *)
(******************************************************************************)

Definition setModuleName (name : string) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule _ insts inputs outputs) lm
     => put (mkCavaState o vecCount vecDefs ext clk clkEdge rst rstEdge (mkModule name insts inputs outputs) lm)
  end.

Definition setClockAndReset (clk_and_edge: Signal Bit * SignalEdge)
                            (rst_and_edge: Signal Bit* SignalEdge)
                            : state CavaState unit :=
  let (clk, clkEdge) := clk_and_edge in
  let (rst, rstEdge) := rst_and_edge in
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs ext _ _ _ _ m lm 
     => put (mkCavaState o vecCount vecDefs ext (Some clk) clkEdge (Some rst) rstEdge m lm)
  end.

Definition getClockAndReset : state CavaState ((option (Signal Bit) * SignalEdge) *
                                               (option (Signal Bit) * SignalEdge)) :=
  cs <- get ;;
  match cs with
  | mkCavaState _ vecCount vecDefs ext clk clkEdge rst rstEdge _ _=>
     ret ((clk, clkEdge), (rst, rstEdge))
  end.

Definition inputBit (name : string) : state CavaState (Signal Bit) :=
  addInputPort (mkPort name Bit) ;;
  ret (NamedWire name).

Definition inputVector (t: SignalType) (sz: nat) (name : string) : state CavaState (Signal (Vec t sz)) :=
  addInputPort (mkPort name (Vec t sz)) ;;
  ret (NamedVector t sz name).

Definition outputBit (name : string) (i : Signal Bit) : state CavaState unit :=
  addOutputPort (mkPort name Bit) ;;
  assignSignal (NamedWire name) i.

Definition outputVector (t: SignalType) (sz : nat) (name : string) (v : Signal (Vec t sz)) : state CavaState unit :=
  addOutputPort (mkPort name (Vec t sz)) ;;
  assignSignal (NamedVector t sz name) v.

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

Definition initStateFrom (startAt : N) : CavaState
  := mkCavaState startAt 0 [] [] None PositiveEdge None PositiveEdge
                 (mkModule "noname" [] [] []) [].

Definition initState : CavaState
  := initStateFrom 0.

(******************************************************************************)
(* Execute a monadic circuit description and return the generated netlist.    *)
(******************************************************************************)

Fixpoint instantiateInputPorts {t : SignalType}
                               (inputs: denotePortDeclarations t)
                               : state CavaState (Signal t) :=
  match t, inputs with
  | Void, _ => ret UndefinedSignal
  | Bit, (name, _) => inputBit name
  | Vec k sz, (name, _) => inputVector k sz name
  | ExternalType t, (name, _) => addInputPort (mkPort name (ExternalType t)) ;;
                                 ret (UninterpretedSignal name)
  | Pair t1 t2, (a, b) => v1 <- instantiateInputPorts a;;
                          v2 <- instantiateInputPorts b;;
                          ret (MkPair v1 v2)
  end.

Fixpoint instantiateOutputPorts {t : SignalType}
                                (outputs: denotePortNames t) 
                                (v: Signal t) : state CavaState unit :=
  match t, outputs, v  with
  | Void, _, _ => ret tt
  | Bit, name, s => outputBit outputs s
  | Vec k sz, name, s => outputVector k sz name s
  | ExternalType t, name, s => addOutputPort (mkPort name (ExternalType t)) ;;
                               assignSignal (UninterpretedSignal name) s
  | Pair t1 t2, (a, b), ab => instantiateOutputPorts a v1 ;;
                              instantiateOutputPorts b v2
  | _, _, _ => ret tt
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

(* driveArguments produces a list of pairs where each element is a name and
   a Signal which is wrapped with UntypedSignal so we can make a list of these
   pairs. This represents port names of a component and the driving expression
   for the named port. This is made by flattening a shape of port declarations
   and driver signals. *)
Fixpoint driveArguments (inputs: @shape (PortDeclaration * UntypedSignal)) : list (string * UntypedSignal) :=
  match inputs with
  | Empty => []
  | One (mkPort name typ, driver) => [(name, driver)]
  | Tuple2 t1 t2 => driveArguments t1 ++ driveArguments t2
  end.

Fixpoint declareOutputs (outputs: @shape PortDeclaration) : state CavaState (signalSmashTy (mapShape port_shape outputs)) :=
  match outputs with
  | Empty => ret tt
  | One (mkPort name typ) =>
      match typ with
      | Void => ret UndefinedSignal
      | Bit => newWire
      | Vec k sz => nv <- newVector k sz ;;
                       ret (smash nv)
      | ExternalType t => newExternal t
      end
  | Tuple2 t1 t2 => o1 <- declareOutputs t1 ;;
                    o2 <- declareOutputs t2 ;;
                    ret (o1, o2)
  end.

Definition wireUpClock (c : option (Signal Bit)) (clkArgName: string) : list (string * UntypedSignal) :=
  match c with
  | None => []
  | Some clk => [(clkArgName, USignal clk)]
  end.

Definition wireUpReset (c : option (Signal Bit)) (rstArgName: string) : list (string * UntypedSignal) :=
  match c with
  | None => []
  | Some rst => [(rstArgName, USignal rst)]
  end.

Definition blackBox (intf : CircuitInterface)
                    (inputs: signalSmashTy (mapShape port_shape (circuitInputs intf))) :
                    state CavaState (signalSmashTy (mapShape port_shape (circuitOutputs intf))) :=
  let inputPortShape : @shape Kind := mapShape port_shape (circuitInputs intf) in
  let shapedInputs := recoverUntypedShape (mapShape port_shape (circuitInputs intf)) inputs in
  let inputParametersWithArguments := zipShapes (circuitInputs intf) shapedInputs in
  let inputPorts : list (string * UntypedSignal) := driveArguments inputParametersWithArguments in
  '((optClk, _), (optRst, _)) <- getClockAndReset ;;
  let clkPort := wireUpClock optClk (clkName intf) in
  let rstPort := wireUpReset optRst (rstName intf) in
  outputSignals <- declareOutputs (circuitOutputs intf) ;;
  let outputPortShape : @shape Kind := mapShape port_shape (circuitOutputs intf) in
  let shapedOutputs := recoverUntypedShape (mapShape port_shape (circuitOutputs intf)) outputSignals in
  let outputParametersWithArguments := zipShapes (circuitOutputs intf) shapedOutputs in
  let outputPorts : list (string * UntypedSignal) := driveArguments outputParametersWithArguments in
  (* For the moment do not automatically insert clock or reset. *)
  (* TODO(satnam): Consider schemes where clock and rest can be threaded through
     in a consistent way. *)
  (* addInstance (Component (circuitName intf) [] (clkPort ++ rstPort ++ inputPorts ++ outputPorts)) ;; *)
  addInstance (Component (circuitName intf) [] (inputPorts ++ outputPorts)) ;;
  ret outputSignals.

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

Fixpoint vec2expr {k sz} (v: signalTy bool (One (Vec k sz))) : SignalExpr :=
  match k, v with
  | Void, _ => NoSignal
  | Bit, zx => VecVal (map BitVal (Vector.to_list zx))
  | Vec k s2, y => VecVal (map (@vec2expr k s2) (Vector.to_list y))
  | ExternalType t, zx => NoSignal
  end.

Fixpoint denoteValueWithSignalExpr (t: @shape Kind) (v: signalTy bool t) : @shape SignalExpr :=
  match t, v with
  | Empty, _ => Empty
  | One Void, x => One NoSignal
  | One Bit, x => One (BitVal x)
  | One (Vec k sz), xs => One (vec2expr xs)
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
