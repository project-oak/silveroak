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

Fixpoint mapShapeM {A B : Type} {m} `{Monad m} (f : A -> m B) (s : @shape A) : m shape :=
  match s with
  | Empty => ret Empty
  | One thing => fv <- f thing ;;
                 ret (One fv)
  | @Tuple2 _ t1 t2 => fv1 <- @mapShapeM A B m _ f t1 ;;
                       fv2 <- @mapShapeM A B m _ f t2 ;; 
                       ret (Tuple2 fv1 fv2)
  end.

Fixpoint zipShapes {A B : Type} (sA : @shape A) (sB : @shape B) : @shape (A * B) :=
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

(******************************************************************************)
(* signalTy maps a shape to a type based on T                                 *)
(******************************************************************************)

Fixpoint signalTy (T : Type) (s : shape) : Type :=
  match s with
  | Empty  => unit
  | One t => portTypeTy T t
  | Tuple2 s1 s2  => prod (signalTy T s1) (signalTy T s2)
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

Inductive Primitive: shape -> shape -> Type :=
  (* I/O port wiring *)
  | WireInputBit:     string -> Primitive Empty (One Bit)
  | WireInputBitVec:  string -> forall {sizes}, Primitive Empty (One (BitVec sizes))
  | WireOutputBit:    string -> Primitive (One Bit) Empty
  | WireOutputBitVec: string -> forall {sizes}, Primitive (One (BitVec sizes)) Empty
  (* SystemVerilog primitive gates. *)
  | Not:       Primitive (One Bit) (One Bit)
  | And:       forall n, Primitive (One (BitVec [n])) (One Bit)
  | Nand:      forall n, Primitive (One (BitVec [n])) (One Bit)
  | Or:        forall n, Primitive (One (BitVec [n])) (One Bit)
  | Nor:       forall n, Primitive (One (BitVec [n])) (One Bit)
  | Xor:       forall n, Primitive (One (BitVec [n])) (One Bit)
  | Xnor:      forall n, Primitive (One (BitVec [n])) (One Bit)
  | Buf:       Primitive (One Bit) (One Bit)
  (* A Cava unit delay bit component. *)
  | DelayBit:  Primitive (One Bit) (One Bit)
  (* Assignment of bit wire *)
  | AssignBit: Primitive (One Bit) (One Bit)
  (* Arithmetic operations *)
  | UnsignedAdd : forall aSize bSize sumSize,
                  Primitive (Tuple2 (One (BitVec [aSize])) (One (BitVec [bSize])))
                            (One (BitVec [sumSize]))
  (* Xilinx FPGA architecture specific gates. *)
  | Xorcy:     Primitive (Tuple2 (One Bit) (One Bit)) (One Bit)
  | Muxcy:     Primitive (Tuple2 (One Bit) (Tuple2 (One Bit) (One Bit))) (One Bit).

(* PrimitiveInstance bound to ports of type N *)
Inductive PrimitiveInstance :=
  | BindPrimitive : forall (i o : shape), Primitive i o -> signalTy N i -> signalTy N o
      -> PrimitiveInstance.

Arguments BindPrimitive [i o].

(* Helper constructors *)
Definition BindNot i o: PrimitiveInstance := BindPrimitive Not i o.

Definition BindAnd  is o: PrimitiveInstance := BindPrimitive (And (length is)) is o.
Definition BindNand is o: PrimitiveInstance := BindPrimitive (Nand (length is)) is o.
Definition BindOr   is o: PrimitiveInstance := BindPrimitive (Or (length is)) is o.
Definition BindNor  is o: PrimitiveInstance := BindPrimitive (Nor (length is)) is o.
Definition BindXor  is o: PrimitiveInstance := BindPrimitive (Xor (length is)) is o.
Definition BindXnor is o: PrimitiveInstance := BindPrimitive (Xnor (length is)) is o.

Definition BindBuf       i o: PrimitiveInstance := BindPrimitive Buf i o.
Definition BindDelayBit  i o: PrimitiveInstance := BindPrimitive DelayBit i o.
Definition BindAssignBit i o: PrimitiveInstance := BindPrimitive AssignBit i o.

Definition BindXorcy i o: PrimitiveInstance := BindPrimitive Xorcy i o.
Definition BindMuxcy i o: PrimitiveInstance := BindPrimitive Muxcy i o.

Definition BindUnsignedAdd (sumSize: nat) is o: PrimitiveInstance :=
                           BindPrimitive (UnsignedAdd (length (fst is)) (length (snd is)) sumSize) is o.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Record PortDeclaration : Type := mkPort {
  port_name : string;
  port_shape : portType;
}.

Notation Netlist := (list PrimitiveInstance).

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

Fixpoint shapeToPortDeclaration (s : @shape (string * portType)) : list PortDeclaration :=
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

(******************************************************************************)
(* Extraction utilities                                                       *)
(******************************************************************************)

Definition primitiveName {i o} (prim: Primitive i o) : option string :=
match prim with
| Not    => Some "not"
| And _  => Some "and"
| Nand _ => Some "nand"
| Or _   => Some "or"
| Nor _  => Some "nor"
| Xor _  => Some "xor"
| Xnor _ => Some "xnor"
| Buf    => Some "buf"
| Xorcy  => Some "XORCY"
| Muxcy  => Some "MUXCY"
| _      => None (* unnameable primitive *)
end%string.

Definition instanceInputs (prim: PrimitiveInstance) : list N :=
match prim with
| BindPrimitive (WireInputBit _) _ _        => []
| BindPrimitive (WireInputBitVec _ ) _ _    => []
| BindPrimitive (WireOutputBit _) i _       => [i]
| BindPrimitive (WireOutputBitVec _) i _    => [] (* Don't use. *)
| BindPrimitive Not i _                     => [i]
| BindPrimitive (And _) i _                 => i
| BindPrimitive (Nand _) i _                => i
| BindPrimitive (Or _) i _                  => i
| BindPrimitive (Nor _) i _                 => i
| BindPrimitive (Xor _) i _                 => i
| BindPrimitive (Xnor _) i _                => i
| BindPrimitive Buf i _                     => [i]
| BindPrimitive Xorcy (x,y) _               => [x; y]
| BindPrimitive Muxcy (i,(t,e)) _           => [i; t; e]
| BindPrimitive DelayBit i _                => [i]
| BindPrimitive AssignBit i _               => [i]
| BindPrimitive (UnsignedAdd _ _ _) (x,y) _ => x ++ y
end.

Definition unsignedAddercomponents (prim: PrimitiveInstance) : option
  (list N * list N * list N)
  :=
match prim with
| BindPrimitive (UnsignedAdd _ _ _) (x,y) z => Some (x, y, z)
| BindPrimitive _ _ _                       => None
end.

Definition instanceArgs (prim: PrimitiveInstance) : option (list N) :=
match prim with
| BindPrimitive (WireInputBit _) _ o        => Some [o]
(*| BindPrimitive (WireInputBitVec _ _) _ o   => Some [o] *)
| BindPrimitive (WireOutputBit _) i _       => Some [i]
(*| BindPrimitive (WireOutputBitVec _) i _  => Some i *)
| BindPrimitive Not i o           => Some [o; i]
| BindPrimitive (And _) i o       => Some (o :: i)
| BindPrimitive (Nand _) i o      => Some (o :: i)
| BindPrimitive (Or _) i o        => Some (o :: i)
| BindPrimitive (Nor _) i o       => Some (o :: i)
| BindPrimitive (Xor _) i o       => Some (o :: i)
| BindPrimitive (Xnor _) i o      => Some (o :: i)
| BindPrimitive Buf i o           => Some [o; i]
| BindPrimitive Xorcy (x,y) o     => Some [o; x; y]
| BindPrimitive Muxcy (i,(t,e)) o => Some [o; i; t; e]
| _ => None
end.
