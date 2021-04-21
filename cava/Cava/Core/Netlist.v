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
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.StateMonad.
Require Export ExtLib.Data.List.
Require Import ExtLib.Data.Option.
Require Import coqutil.Datatypes.HList.

Import ListNotations.
Import MonadNotation.
Import FunctorNotation.
Import ApplicativeNotation.
Open Scope string_scope.
Open Scope list_scope.
Open Scope monad_scope.

Require Import Cava.Core.Signal.
Require Import Cava.Util.Tuple.

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
  | Delay:     forall (t : SignalType), combType t -> Signal t -> Signal t -> Instance
  (* Composite delay component with enable i.e. a register with clock enable *)
  | DelayEnable: forall (t : SignalType),
                 combType t -> Signal Bit -> Signal t -> Signal t -> Instance
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

Definition port_netlistsignal (x: PortDeclaration) : Type := Signal (port_type x).
Definition port_value (x: PortDeclaration) : Type := combType (port_type x).

Record Module : Type := mkModule {
  moduleName : string;
  netlist : Netlist;
  inputs :  list PortDeclaration;
  outputs : list PortDeclaration;
}.

Inductive TaggedEdge (T: Type) :=
  | mkTaggedEdge: T -> SignalEdge -> TaggedEdge T.
Arguments mkTaggedEdge {T}.

Global Instance Functor_TaggedEdge : Functor TaggedEdge :=
{| fmap := fun _ _ f x =>
    match x with
    | mkTaggedEdge x edge => mkTaggedEdge (f x) edge
    end
|}.

Definition getTag {T} '((mkTaggedEdge x _): TaggedEdge T) := x.

Record CircuitInterface : Type := mkCircuitInterface {
  circuitName           : string;
  clk : option (TaggedEdge string);
  rst : option (TaggedEdge string);
  circuitInputs          : list PortDeclaration;
  circuitOutputs         : list PortDeclaration;
}.

Definition sequentialInterface (circuitName: string)
                               (clkName: string) (clkEdge: SignalEdge)
                               (rstName: string) (rstEdge: SignalEdge)
                               (circuitInputs: list PortDeclaration)
                               (circuitOutputs: list PortDeclaration) :=
  mkCircuitInterface circuitName (Some (mkTaggedEdge clkName clkEdge)) (Some (mkTaggedEdge rstName rstEdge))
                     circuitInputs circuitOutputs.

Definition combinationalInterface (circuitName: string)
                                  (circuitInputs: list PortDeclaration)
                                  (circuitOutputs: list PortDeclaration) :=
  mkCircuitInterface circuitName None None circuitInputs circuitOutputs.

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
  clock : option (TaggedEdge (Signal Bit));
  reset : option (TaggedEdge (Signal Bit));
  module : Module; (* The top level module. *)
  libraryModules : list (CircuitInterface * Module);
                   (* Dependent modules of the root module. *)
}.

Definition newWire : state CavaState (Signal Bit) :=
  cs <- get;;
  match cs with
  | mkCavaState o vCount vDefs ext clk rst m lm
      => put (mkCavaState (o+1) vCount vDefs ext clk rst m lm) ;;
         ret (Wire o)
  end.

Definition newWires (width : nat) : state CavaState (list (Signal Bit)) :=
  cs <- get ;;
  match cs with
  | mkCavaState o vCount vDefs ext clk rst m lm =>
      let outv := map N.of_nat (seq (N.to_nat o) width) in
      put (mkCavaState (o + N.of_nat width) vCount vDefs ext clk rst m lm) ;;
      ret (map Wire outv)
  end.

Definition newVector (t : SignalType) (s: nat) : state CavaState (Signal (Vec t s)) :=
  cs <- get ;;
  match cs with
  | mkCavaState o vCount vDefs ext clk rst m ml =>
      put (mkCavaState o (vCount + 1) (vDefs ++ [(t, s)]) ext clk rst m ml) ;;
      ret (LocalVec t s vCount)
  end.

Definition newExternal (t : string) : state CavaState (Signal (ExternalType t)) :=
  cs <- get ;;
  match cs with
  | mkCavaState o vCount vDefs ext clk rst m ml =>
    let newExt := UninterpretedSignalIndex t (N.of_nat (length ext)) in
    put (mkCavaState o vCount vDefs (ext ++ [t]) clk rst m ml) ;;
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
  | mkCavaState o vecCount vecDefs ext clk rst (mkModule name insts inputs outputs) lm
    => put (mkCavaState o vecCount vecDefs ext clk rst (mkModule name (newInst::insts) inputs outputs) lm)
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
  | mkCavaState o vecCount vecDefs ext clk rst (mkModule name insts inputs outputs) lm
    => ret insts
  end.

Definition setInstances (insts: list Instance) : state CavaState unit :=
cs <- get;;
  match cs with
  | mkCavaState o vecCount vecDefs ext clk rst (mkModule name _ inputs outputs) lm
    => put (mkCavaState o vecCount vecDefs ext clk rst (mkModule name insts inputs outputs) lm)
  end.

Definition assignSignal {k} (s1: Signal k) (s2: Signal k) :=
  addInstance (AssignSignal s1 s2).

Definition addInputPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match newPort with
  | mkPort "" _ => ret tt (* Clock or reset not used *)
  | _ => match cs with
         | mkCavaState o vecCount vecDefs ext clk rst (mkModule n insts inputs outputs) lm =>
           put (mkCavaState o vecCount vecDefs ext clk rst (mkModule n insts (cons newPort inputs) outputs) lm)
         end
  end.

Definition addOutputPort (newPort: PortDeclaration) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs ext clk rst (mkModule n insts inputs outputs) lm =>
      put (mkCavaState o vecCount vecDefs ext clk rst (mkModule n insts inputs (cons newPort outputs)) lm)
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
    | mkCavaState o vecCount vecDefs ext clk rst m lm =>
        if findModule (circuitName intf) lm then
          ret tt
        else
          put (mkCavaState o vecCount vecDefs ext clk rst m
               (lm ++ [(intf, newModule)]))
    end.

(******************************************************************************)
(* Define netlist functions used to specify top-level module behaviour.       *)
(******************************************************************************)

Definition setModuleName (name : string) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs ext clk rst (mkModule _ insts inputs outputs) lm
     => put (mkCavaState o vecCount vecDefs ext clk rst (mkModule name insts inputs outputs) lm)
  end.

Definition setClockAndReset (clk: option (TaggedEdge (Signal Bit)))
                            (rst: option (TaggedEdge (Signal Bit)))
                            : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o vecCount vecDefs ext _ _ m lm
     => put (mkCavaState o vecCount vecDefs ext clk rst m lm)
  end.

Definition getClockAndReset : state CavaState ((option (TaggedEdge (Signal Bit))) *
                                               (option (TaggedEdge (Signal Bit)))) :=
  cs <- get ;;
  match cs with
  | mkCavaState _ vecCount vecDefs ext clk rst _ _ =>
     ret (clk, rst)
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
  := mkCavaState startAt 0 [] [] None None
                 (mkModule "noname" [] [] []) [].

Definition initState : CavaState
  := initStateFrom 0.

(******************************************************************************)
(* Execute a monadic circuit description and return the generated netlist.    *)
(******************************************************************************)

Definition addOptionalInputPort o :=
  match o with
  | Some x => addInputPort (mkPort (getTag x) Bit)
  | None => ret tt
  end.

Definition instantiateInputPort
  (port : PortDeclaration)
  : state CavaState (port_netlistsignal port) :=
  let name := port_name port in
  match port_type port as s return state CavaState (Signal s) with
  | Void => ret UndefinedSignal
  | Bit => inputBit name
  | Vec k sz => inputVector k sz name
  | ExternalType t =>
    addInputPort (mkPort name (ExternalType t)) ;;
    ret (UninterpretedSignal name)
  end.

Fixpoint instantiateInputPorts {o}
  (ports : list PortDeclaration):
  curried (port_netlistsignal <$> ports) (state CavaState o) -> state CavaState o :=
  match ports with
  | [] => fun circuit => circuit
  | x::xs => fun circuit =>
    i <- instantiateInputPort x ;;
    instantiateInputPorts xs (circuit i)
  end.

Definition instantiateOutputPort
  (port : PortDeclaration)
  : port_netlistsignal port -> state CavaState unit :=
  let name := port_name port in
  match port_type port as s return Signal s -> state CavaState unit with
  | Void => fun _ => ret tt
  | Bit => fun port => outputBit name port
  | Vec k sz => fun port => outputVector k sz name port
  | ExternalType t => fun s =>
    addOutputPort (mkPort name (ExternalType t)) ;;
    assignSignal (UninterpretedSignal name) s
  end.

Fixpoint instantiateOutputPorts
  (ports : list PortDeclaration):
  tupledR (port_netlistsignal <$> ports) -> state CavaState unit :=
  match ports with
  | [] => ret
  | x::xs =>
      fun '( (y,ys) : tupledR (port_netlistsignal <$> (x :: xs))) =>
      instantiateOutputPort x y;; instantiateOutputPorts xs ys
  end.

Definition wireUpCircuit
  (intf : CircuitInterface)
  (circuit :
    let inputs := port_netlistsignal <$> (circuitInputs intf) in
    let outputs := port_netlistsignal <$> (circuitOutputs intf) in
    curried inputs (state CavaState (tupled' outputs)))
  : state CavaState unit :=
  setModuleName (circuitName intf) ;;
  setClockAndReset (fmap NamedWire <$> clk intf) (fmap NamedWire <$> rst intf) ;;
  addOptionalInputPort (clk intf) ;;
  addOptionalInputPort (rst intf) ;;
  o <- instantiateInputPorts (circuitInputs intf) circuit ;;
  instantiateOutputPorts _ (unbalance' _ o).

Definition makeNetlist (intf : CircuitInterface) circuit : CavaState :=
  let inputs := port_netlistsignal <$> (circuitInputs intf) in
  let outputs := tupled' (port_netlistsignal <$> (circuitOutputs intf)) in
  execState (wireUpCircuit intf (curry inputs _ (uncurried_to_uncurriedR _ _ circuit))) initState.

Check makeNetlist.

                        (* makeNetlist intf (curry _ _ (curry_helper _ _ (interpCircuit c))). *)
Definition makeNetlist' (intf : CircuitInterface) circuit : CavaState
  := execState (wireUpCircuit intf circuit) initState.

(* driveArguments produces a list of pairs where each element is a name and
   a Signal which is wrapped with UntypedSignal so we can make a list of these
   pairs. This represents port names of a component and the driving expression
   for the named port. This is made by flattening a shape of port declarations
   and driver signals. *)

Fixpoint driveArgumentsR (inputPorts: list PortDeclaration) :
                          tupledR (port_netlistsignal <$> inputPorts) ->
                          list (string * UntypedSignal) :=
  match inputPorts with
  | [] => fun _ => []
  | x::xs =>
      fun '( (y,ys) : tupledR (port_netlistsignal <$> (x :: xs))) =>
      (port_name x, USignal y) :: driveArgumentsR xs ys
  end.

Definition declareOutput (output : PortDeclaration) : state CavaState (port_netlistsignal output) :=
  match port_type output as s return state CavaState (Signal s) with
  | Void => ret UndefinedSignal
  | Bit => newWire
  | Vec k sz => newVector k sz
  | ExternalType t => newExternal t
  end.

Fixpoint declareOutputsR (outputs: list PortDeclaration)
  : state CavaState (tupledR (port_netlistsignal <$> outputs)) :=
  match outputs with
  | [] => ret tt
  | x::xs =>
    xi <- declareOutput x ;;
    xr <- declareOutputsR xs ;;
    ret (xi, xr)
  end.

Definition rewire (c : Signal Bit) (newName: string) : (string * UntypedSignal) :=
  (newName, USignal c).

Definition optionToList {A} (o: option A): list A :=
  match o with Some x => [x] | None => [] end.

Definition blackBoxNet' (intf : CircuitInterface)
                       (inputs: tupledR (port_netlistsignal <$> circuitInputs intf)) :
                       state CavaState (tupledR (port_netlistsignal <$> circuitOutputs intf)) :=
  let inputPorts : list (string * UntypedSignal) := driveArgumentsR (circuitInputs intf) inputs in
  '(optClk, optRst) <- getClockAndReset ;;
  outputSignals <- declareOutputsR (circuitOutputs intf) ;;
  let clkPort := rewire <$> (fmap getTag optClk) <*> (fmap getTag (clk intf)) in
  let rstPort := rewire <$> (fmap getTag optRst) <*> (fmap getTag (rst intf)) in
  let outputPorts : list (string * UntypedSignal) := driveArgumentsR (circuitOutputs intf) outputSignals in
  (* TODO(satnam): Consider schemes where clock and rest can be threaded through
     in a consistent way. *)
  (* This currently does not check that the clock/reset have the correct
   * polarity *)
  addInstance (Component (circuitName intf) [] (optionToList clkPort ++ optionToList rstPort ++ inputPorts ++ outputPorts)) ;;
  ret outputSignals.

Definition blackBoxNet (intf : CircuitInterface)
                       (inputs: tupled' (port_netlistsignal <$> circuitInputs intf)) :
                       state CavaState (tupled' (port_netlistsignal <$> circuitOutputs intf)) :=
  o <- blackBoxNet' intf (unbalance' _ inputs) ;;
  ret (rebalance' _ o).

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

Fixpoint tupleToSignalExprR (pd: list PortDeclaration) :
                            tupledR (port_value <$> pd) ->
                            list SignalExpr :=
  match pd with
  | [] => fun _ => []
  | x::xs =>
      fun '( (y,ys) : tupledR (port_value <$> (x :: xs))) =>
      toSignalExpr (port_type x) y :: tupleToSignalExprR xs ys
  end.

Definition testBench (name : string)
                     (intf : CircuitInterface)
                     (testInputs : list (tupled' (port_value <$> circuitInputs intf)))
                     (testExpectedOutputs : list (tupled' (port_value <$> circuitOutputs intf)))
  :=
  let inputs := unbalance' (port_value <$> circuitInputs intf) <$> testInputs in
  let outputs := unbalance' (port_value <$> circuitOutputs intf) <$> testExpectedOutputs in
  mkTestBench name intf
    (map (tupleToSignalExprR (circuitInputs intf)) inputs)
    (map (tupleToSignalExprR (circuitOutputs intf)) outputs).


(* Haskell helper functions *)
Definition incN (n: N) : N := n + 1.

