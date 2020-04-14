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

From Coq Require Import Ascii String.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
From Coq Require Import Vector.
From Coq Require Import Bool.Bool.
From Coq Require Import Numbers.NaryFunctions.

Require Import Omega.

Import ListNotations.

(* shape describes the shape of the wires coming into our out of a circuit
   block.
*)

Inductive shape {A: Type} : Type :=
  | Empty : shape
  | One : A -> shape
  | Tuple2 : shape -> shape -> shape (* A pair of bundles of wires *).

Notation "\u2039 x , y \u203a" := (Tuple2 x y).

Inductive type : Type :=
  | Bit : type                (* A single wire *)
  | BitVec : list nat -> type (* Multi-dimensional bit-vectors *).


Fixpoint bitVecTy {A : Type} (T : Type) (n : list A) : Type :=
  match n with
  | [] => list T
  | [x] => list T
  | x::xs => list (bitVecTy T xs)
  end.

Compute bitVecTy N [3].
Compute bitVecTy N [3; 2].

Definition typeTy (T : Type) (t : type) : Type :=
  match t with
  | Bit => T
  | BitVec v => bitVecTy T v
  end.

Fixpoint signalTy (T : Type) (s : shape) : Type :=
  match s with
  | Empty  => unit
  | One t => typeTy T t
  | Tuple2 s1 s2  => signalTy T s1 * signalTy T s2
  end.

(******************************************************************************)
(* PrimitiveInstance elements                                                 *)
(******************************************************************************)

(* The primitive elements that can be instantiated in Cava. Some are generic
   SystemVerilog gates that can be used with synthesis and back-end tools to
   map to any architecture, while others are specific to Xilinx FPGAs.
*)

Inductive Primitive: shape -> shape -> Type :=
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
  port_shape : shape;
  port_type : signalTy N port_shape;
}.

Notation Netlist := (list PrimitiveInstance).

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

Definition instanceNumber (prim: PrimitiveInstance) : option N :=
match prim with
| BindPrimitive (UnsignedAdd _ _ _) _ _ => None
| BindPrimitive _ _ o                   => Some o
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
