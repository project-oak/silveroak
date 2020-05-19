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

(******************************************************************************)
(* shape describes the types of wires going into or out of a Cava circuit,    *)
(* but not all shapes can be bound to a SystemVerilog port name. Those that   *)
(* can are identified by the One constructor.                                 *)
(******************************************************************************)

Inductive shape {A: Type} : Type :=
  | Empty : shape
  | One : A -> shape
  | Tuple2 : shape -> shape -> shape. (* A pair of bundles of wires *)

(* General tuples can be mapped to Tuple2 *)

(* TODO(satnam): It would be more useful to build a left-associative
   tuple.
*)
Fixpoint tuple {A: Type} (t : list shape) : shape :=
  match t with
  | [] => Empty
  | [x] => x
  | x::xs => @Tuple2 A x (tuple xs)
  end.

(* Supporting mapping over a shape. *)

Fixpoint mapShape {A B : Type} (f : A -> B) (s : @shape A) : @shape B :=
  match s with
  | Empty => Empty
  | One thing => One (f thing)
  | Tuple2 t1 t2 => Tuple2 (mapShape f t1) (mapShape f t2)
  end.

Fixpoint mapShapeM {A B : Type} {m} `{Monad m} (f : A -> m B) (s : @shape A) :
                  m shape :=
  match s with
  | Empty => ret Empty
  | One thing => fv <- f thing ;;
                 ret (One fv)
  | @Tuple2 _ t1 t2 => fv1 <- @mapShapeM A B m _ f t1 ;;
                       fv2 <- @mapShapeM A B m _ f t2 ;;
                       ret (Tuple2 fv1 fv2)
  end.

Fixpoint zipShapes {A B : Type} (sA : @shape A) (sB : @shape B) :
                   @shape (A * B) :=
  match sA, sB with
  | Empty, Empty => Empty
  | One a, One b => One (a, b)
  | Tuple2 t1 t2, Tuple2 t3 t4 => Tuple2 (zipShapes t1 t3) (zipShapes t2 t4)
  | _, _ => Empty
  end.

Fixpoint flattenShape {A} (s : @shape A) : list A :=
  match s with
  | Empty => []
  | One thing => [thing]
  | Tuple2 t1 t2 =>  flattenShape t1 ++ flattenShape t2
  end.

(******************************************************************************)
(* Values of portType can occur as the type of signals on a circuit interface *)
(******************************************************************************)

Inductive portType : Type :=
  | Bit : portType                (* A single wire *)
  | BitVec : list nat -> portType (* Multi-dimensional bit-vectors *).

Fixpoint bitVecTy {A : Type} (T : Type) (n : list A) : Type :=
  match n with
  | [] => T
  | [x] => list T
  | x::xs => list (bitVecTy T xs)
  end.

Definition portTypeTy (T : Type) (t : portType) : Type :=
  match t with
  | Bit => T
  | BitVec v => bitVecTy T v
  end.

Fixpoint bitsInPort (p : portType) : nat :=
  match p with
  | Bit => 1
  | BitVec xs => fold_left (fun x y => x * y) xs 1
  end.

Fixpoint bitsInPortShape (s : @shape portType) : nat :=
  match s with
  | Empty => 0
  | One typ => bitsInPort typ
  | Tuple2 t1 t2 => bitsInPortShape t1 + bitsInPortShape t2
  end.

(* The duplicated i and l parametere are a temporary work-around to allow
   well-founded recursion to be recognized.
   TODO(satnam): Rewrite with an appropriate well-foundedness proof.
*)
Fixpoint numberBitVec (offset : N) (i : list nat) (l : list nat) : @bitVecTy nat N l :=
  match l, i return @bitVecTy nat N l with
  | [], _         => 0%N
  | [x], [_]      => map N.of_nat (seq (N.to_nat offset) x)
  | x::xs, p::ps  => let z := N.of_nat (fold_left (fun x y => x * y) xs 1) in
                     map (fun w => numberBitVec (offset+w*z) ps xs) (map N.of_nat (seq 0 x))
  | _, _          => []
  end.

Fixpoint mapBitVec {A B} (f: A -> B) (i : list nat) (l : list nat) : @bitVecTy nat A l -> @bitVecTy nat B l :=
  match l, i  return @bitVecTy nat A l -> @bitVecTy nat B l with
  | [], _         => f
  | [x], [_]      => map f
  | x::xs, p::ps  => map (mapBitVec f ps xs)
  | _, _          => fun _ => []
  end.

Fixpoint zipBitVecs {A B} (i : list nat) (l : list nat)
  : @bitVecTy nat A l -> @bitVecTy nat B l -> @bitVecTy nat (A*B) l :=
  match l, i  return @bitVecTy nat A l -> @bitVecTy nat B l -> @bitVecTy nat (A*B) l with
  | [], _         => pair
  | [x], [_]      => fun ms ns => combine ms ns
  | x::xs, p::ps  => fun ms ns => map (fun '(m,n) => zipBitVecs ps xs m n) (combine ms ns)
  | _, _          => fun _ _ => []
  end.

Fixpoint flattenBitVec {A} (i : list nat) (l : list nat)
  : @bitVecTy nat A l -> list A :=
  match l, i  return @bitVecTy nat A l -> list A with
  | [], _         => fun z => [z]
  | [x], [_]      => fun zs => zs
  | x::xs, p::ps  => fun zs => concat (map (flattenBitVec ps xs) zs)
  | _, _          => fun _ => []
  end.

Definition flattenPort {A} (port: portType) (x: portTypeTy A port) : list A :=
  match port, x with
  | Bit, _ => [x]
  | BitVec sz, _ => flattenBitVec sz sz x
  end.

(******************************************************************************)
(* signalTy maps a shape to a type based on T                                 *)
(******************************************************************************)

Fixpoint signalTy (T : Type) (s : shape) : Type :=
  match s with
  | Empty  => unit
  | One t => portTypeTy T t
  | Tuple2 s1 s2  => prod (signalTy T s1) (signalTy T s2)
  end.

Fixpoint numberPort (i : N) (inputs : @shape portType) : signalTy N inputs :=
  match inputs return signalTy N inputs with
  | Empty => tt
  | One typ =>
      match typ return portTypeTy N typ with
      | Bit => i
      | BitVec xs => numberBitVec i xs xs
      end
  | Tuple2 t1 t2 => let t1Size := bitsInPortShape t1 in
                    (numberPort i t1,  numberPort (i + N.of_nat t1Size) t2)
  end.

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

(* The primitive elements that can be instantiated in Cava. Some are generic
   SystemVerilog gates that can be used with synthesis and back-end tools to
   map to any architecture, while others are specific to Xilinx FPGAs.
*)

Inductive Instance : Type :=
  (* I/O port wiring *)
  | WireInputBit:     string -> N -> Instance
  | WireInputBitVec:  forall sizes, string ->
                      @bitVecTy nat N sizes -> Instance
  | WireOutputBit:    string -> N -> Instance
  | WireOutputBitVec: forall sizes, string ->
                      @bitVecTy nat N sizes -> Instance
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
  (* Xilinx FPGA architecture specific gates. *)
  | Lut1:      N -> N -> N -> Instance
  | Lut2:      N -> N -> N -> N -> Instance
  | Lut3:      N -> N -> N -> N -> N -> Instance
  | Lut4:      N -> N -> N -> N -> N -> N -> Instance
  | Lut5:      N -> N -> N -> N -> N -> N -> N -> Instance
  | Lut6:      N -> N -> N -> N -> N -> N -> N -> N -> Instance                
  | Xorcy:     N -> N -> N -> Instance
  | Muxcy:     N -> N -> N -> N -> Instance.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Record PortDeclaration : Type := mkPort {
  port_name : string;
  port_shape : portType;
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
  circuitInputs  : @shape (string * portType);
  circuitOutputs : @shape (string * portType);
  attributes : list CircuitAttribute;
}.

Fixpoint shapeToPortDeclaration (s : @shape (string * portType)) :
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
