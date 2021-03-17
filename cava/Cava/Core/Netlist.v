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

Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.StateMonad.
Require Export ExtLib.Data.List.

Import ListNotations.
Import MonadNotation.
Open Scope string_scope.
Open Scope list_scope.
Open Scope monad_scope.

Require Import Cava.Core.Signal.

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
  (* Composite delay component i.e. a register *)
  | Delay:     forall (t : SignalType), Signal t -> Signal t -> Signal t -> Instance
  (* Composite delay component with enable i.e. a register with clock enable *)
  | DelayEnable: forall (t : SignalType),
                 Signal t -> Signal Bit -> Signal t -> Signal t -> Instance
  (* Assignment *)
  | AssignSignal: forall {k: SignalType}, Signal k -> Signal k -> Instance
  (* TODO(satnam): Switch to using tupleInterface instead of UntypedSignal *)
  | Component: string ->
               list (string * ConstExpr) ->
               list (string * UntypedSignal) ->
               Instance.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Notation Netlist := (list Instance).

Record PortDeclaration : Type := mkPort {
  port_name : string;
  port_type : SignalType;
}.

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
  circuitInputs          : list PortDeclaration;
  circuitOutputs         : list PortDeclaration;
  attributes             : list CircuitAttribute;
}.

Definition sequentialInterface (circuitName: string)
                               (clkName: string) (clkEdge: SignalEdge)
                               (rstName: string) (rstEdge: SignalEdge)
                               (circuitInputs: list PortDeclaration)
                               (circuitOutputs: list PortDeclaration) :=
  mkCircuitInterface circuitName clkName clkEdge rstName rstEdge
                     circuitInputs circuitOutputs [].

Definition combinationalInterface (circuitName: string)
                                  (circuitInputs: list PortDeclaration)
                                  (circuitOutputs: list PortDeclaration) :=
  sequentialInterface circuitName "" PositiveEdge
                                  "" PositiveEdge
                                  circuitInputs circuitOutputs.

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

Definition newSignal (t: SignalType) : state CavaState (Signal t) :=
  match t with
  | Void => ret UndefinedSignal
  | Bit => newWire
  | Vec k s => newVector k s
  | ExternalType typeName => newExternal typeName
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

Definition instantiateInputPort' (name : string) (port_type : SignalType)
  : state CavaState (Signal port_type) :=
  match port_type with
  | Void => ret UndefinedSignal
  | Bit => inputBit name
  | Vec k sz => inputVector k sz name
  | ExternalType t => addInputPort (mkPort name (ExternalType t)) ;;
                     ret (UninterpretedSignal name)
  end.
Definition instantiateInputPort (input : PortDeclaration)
  : state CavaState (Signal (port_type input)) :=
  instantiateInputPort' (port_name input) (port_type input).

Local Open Scope list_scope.

(* Specialized versions of tuple-operations for signal nets. *)

Definition tupleNetInterface (pds : list PortDeclaration)
  := tupleInterface denoteSignal (map port_type pds).


Definition tupleNetInterfaceR (pds : list PortDeclaration)
  := tupleInterfaceR denoteSignal (map port_type pds).

Definition rebalanceNet (pds : list PortDeclaration)
  := rebalance denoteSignal (map port_type pds).

Definition unbalanceNet (pds : list PortDeclaration)
  := unbalance denoteSignal (map port_type pds).

(* Instantiate input ports, producing a right associative tuple terminated
   with a unit. *)
Fixpoint instantiateInputPortsR (inputs: list PortDeclaration)
  : state CavaState (tupleNetInterfaceR inputs) :=
  match inputs with
  | [] => ret tt
  | x::xs =>
    xi <- instantiateInputPort x ;;
    xr <- instantiateInputPortsR xs ;;
    ret (xi, xr)
  end.

(* Instantiate input ports with a left associative tuple and no unit. *)
Definition instantiateInputPorts (inputs: list PortDeclaration)
  : state CavaState (tupleNetInterface inputs) :=
  right_unit_tuple <- instantiateInputPortsR inputs ;;
  ret (rebalanceNet inputs right_unit_tuple).

Definition instantiateOutputPort' (name : string) (port_type : SignalType)
  : Signal port_type -> state CavaState unit :=
  match port_type as t0 return Signal t0 -> _ with
  | Void => fun _ => ret tt
  | Bit => fun s => outputBit name s
  | Vec k sz => fun s => outputVector k sz name s
  | ExternalType t => fun s => addOutputPort (mkPort name (ExternalType t)) ;;
                           assignSignal (UninterpretedSignal name) s
  end.
Definition instantiateOutputPort (pd : PortDeclaration)
                                 (o : Signal (port_type pd))
  : state CavaState unit :=
  instantiateOutputPort' (port_name pd) (port_type pd) o.

(* instantiateOutputPorts will take a list of port declarations and a bunch
   of signals which are right-associated and match up the elements of the
  port declarations in the list outputPorts with the corresponding driver
  signal and wire up the appropriate port. This function can't be used
  directly by the netlist functions because they expect the top-level
  circuit tuples to use left-associative tuples that match denoteInterfaceL.
*)

Fixpoint instantiateOutputPortsR (outputPorts: list PortDeclaration) :
                                 tupleNetInterfaceR outputPorts ->
                                 state CavaState unit :=
  match outputPorts with
  | [] => fun _ => ret tt
  | x::xs => (match xs as xs0 return ((tupleNetInterfaceR xs0 -> state CavaState unit) -> tupleNetInterfaceR (x::xs0) -> state CavaState unit) with
              | [] => fun _ => fun ab => instantiateOutputPort x (fst ab) (* Discard unit value in second element. *)
              | y::ys => fun (rec: tupleNetInterfaceR (y::ys) -> state CavaState unit) =>
                           fun (ab : tupleNetInterfaceR (x::y::ys)) => instantiateOutputPort x (fst ab);;
                                                                       rec (snd ab)
              end) (instantiateOutputPortsR xs)
  end.

Definition instantiateOutputPorts (outputPorts: list PortDeclaration)
                                  (v: tupleNetInterface outputPorts) :
                                  state CavaState unit :=
  instantiateOutputPortsR outputPorts (unbalanceNet outputPorts v).


Definition wireUpCircuit (intf : CircuitInterface)
                         (circuit : tupleNetInterface (circuitInputs intf) ->
                                    state CavaState (tupleNetInterface (circuitOutputs intf)))
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
                        (circuit : tupleNetInterface (circuitInputs intf) ->
                                    state CavaState (tupleNetInterface (circuitOutputs intf))) : CavaState
  := execState (wireUpCircuit intf circuit) initState.

(* driveArguments produces a list of pairs where each element is a name and
   a Signal which is wrapped with UntypedSignal so we can make a list of these
   pairs. This represents port names of a component and the driving expression
   for the named port. This is made by flattening a shape of port declarations
   and driver signals. *)

Fixpoint driveArgumentsR (inputPorts: list PortDeclaration) :
                          tupleNetInterfaceR inputPorts ->
                          list (string * UntypedSignal) :=
  match inputPorts with
  | [] => fun _ => []
  | x::xs => (match xs as xs0 return ((tupleNetInterfaceR xs0 -> list (string * UntypedSignal)) -> tupleNetInterfaceR (x::xs0) -> list (string * UntypedSignal)) with
              | [] => fun _ => fun (ab : Signal (port_type x) * unit) => [(port_name x, USignal (fst ab))]
              | y::ys => fun (rec: tupleNetInterfaceR (y::ys) -> list (string * UntypedSignal)) =>
                           fun (ab : tupleNetInterfaceR (x::y::ys)) =>
                              (port_name x, USignal (fst ab)) :: rec (snd ab)
              end) (driveArgumentsR xs)
  end.

Definition driveArguments (inputPorts: list PortDeclaration)
                         (v: tupleNetInterface inputPorts)
                         : list (string * UntypedSignal) :=
  driveArgumentsR inputPorts (unbalanceNet inputPorts v).

Definition declareOutput (output : PortDeclaration) : state CavaState (Signal (port_type output)) :=
  match port_type output with
  | Void => ret UndefinedSignal
  | Bit => newWire
  | Vec k sz => newVector k sz
  | ExternalType t => newExternal t
  end.

Fixpoint declareOutputsR (outputs: list PortDeclaration)
  : state CavaState (tupleNetInterfaceR outputs) :=
  match outputs with
  | [] => ret tt
  | x::xs =>
    xi <- declareOutput x ;;
    xr <- declareOutputsR xs ;;
    ret (xi, xr)
  end.

Definition declareOutputs (outputs: list PortDeclaration)
  : state CavaState (tupleNetInterface outputs) :=
  o <- declareOutputsR outputs ;;
  ret (rebalanceNet outputs o).

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

Definition blackBoxNet (intf : CircuitInterface)
                       (inputs: tupleNetInterface (circuitInputs intf)) :
                       state CavaState (tupleNetInterface (circuitOutputs intf)) :=
  let inputPorts : list (string * UntypedSignal) := driveArguments (circuitInputs intf) inputs in
  '((optClk, _), (optRst, _)) <- getClockAndReset ;;
  outputSignals <- declareOutputs (circuitOutputs intf) ;;
  let clkPort := wireUpClock optClk (clkName intf) in
  let rstPort := wireUpReset optRst (rstName intf) in
  let outputPorts : list (string * UntypedSignal) := driveArguments (circuitOutputs intf) outputSignals in
  (* TODO(satnam): Consider schemes where clock and rest can be threaded through
     in a consistent way. *)
  (* This currently does not check that the clock/reset have the correct
   * polarity *)
  let prefix :=
    (if String.eqb (clkName intf) "" then [] else clkPort) ++
    (if String.eqb (rstName intf)  "" then [] else rstPort) in

  addInstance (Component (circuitName intf) [] (prefix ++ inputPorts ++ outputPorts)) ;;
  ret outputSignals.

Record TestBench : Type := mkTestBench {
  testBenchName            : string;
  testBenchInterface       : CircuitInterface;
  testBenchInputs          : list (list SignalExpr);
  testBenchExpectedOutputs : list (list SignalExpr);
}.

Fixpoint toSignalExpr (t: SignalType) (v: combType t) : SignalExpr :=
  match t, v with
  | Void, _ => NoSignal
  | Bit, v => BitVal v
  | Vec vt _, y => VecVal (map (toSignalExpr vt) (Vector.to_list y))
  | ExternalType t, zx => NoSignal
  end.

(* Specialize the tuple operations to work over signal values. *)

Definition tupleSimInterface (pds : list PortDeclaration)
  := tupleInterface combType (map port_type pds).

Definition tupleSimInterfaceR (pds : list PortDeclaration)
  := tupleInterfaceR combType (map port_type pds).

Definition rebalanceSim (pds : list PortDeclaration)
  := rebalance combType (map port_type pds).

Definition unbalanceSim (pds : list PortDeclaration)
  := unbalance combType (map port_type pds).

Fixpoint tupleToSignalExprR (pd: list PortDeclaration) :
                            tupleSimInterfaceR pd ->
                            list SignalExpr :=
  match pd with
  | [] => fun _ => []
  | x::xs => (match xs as xs0 return ((tupleSimInterfaceR xs0 -> list SignalExpr) -> tupleSimInterfaceR (x::xs0) ->  list SignalExpr) with
              | [] => fun _ => fun (ab : combType (port_type x) * unit) => [toSignalExpr (port_type x) (fst ab)]
              | y::ys => fun (rec: tupleSimInterfaceR (y::ys) -> list SignalExpr) =>
                  fun (ab : tupleSimInterfaceR (x::y::ys)) => toSignalExpr (port_type x) (fst ab) :: rec (snd ab)
              end) (tupleToSignalExprR xs)
  end.

Definition tupleToSignalExpr (pd: list PortDeclaration)
                             (v: tupleSimInterface pd) :
                             list SignalExpr :=
  tupleToSignalExprR pd (unbalanceSim pd v).

Definition testBench (name : string)
                     (intf : CircuitInterface)
                     (testInputs : list ((tupleSimInterface (circuitInputs intf))))
                     (testExpectedOutputs : list (tupleSimInterface (circuitOutputs intf)))
  := mkTestBench name intf (map (tupleToSignalExpr (circuitInputs intf)) testInputs)
                           (map (tupleToSignalExpr (circuitOutputs intf)) testExpectedOutputs).
