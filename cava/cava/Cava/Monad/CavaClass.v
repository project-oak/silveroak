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

From Coq Require Vector.
Require Import ExtLib.Structures.Monads.

From Cava Require Import Kind.

Fixpoint denoteVecKind (bit: Type) (vec: Type -> nat -> Type) (k: Kind) : Type :=
  match k with
  | Bit => bit
  | BitVec k2 s => vec (denoteVecKind bit vec k2) s
  | _ => unit
  end.

(* The Cava class represents circuit graphs with Coq-level inputs and
   outputs, but does not represent the IO ports of circuits. This allows
   us to define both circuit netlist interpretations for the Cava class
   as well as behavioural interpretations for attributing semantics. *)
Class Cava m `{Monad m} bit (vec: Kind -> nat -> Type) := {
  denoteKind: Kind -> Type;
  denoteKindV: forall {k s}, denoteKind (BitVec k s) = vec k s;
  vecBoolList: forall {s: nat}, Vector.t bit s -> vec Bit s;
  vecList : forall {k: Kind} {s: nat}, Vector.t (denoteKind k) s ->
            vec k s;
  (* Convert a dynamic vector to a "static" list *)
  vecToList: forall {k: Kind} {s: nat}, vec k s -> list (denoteKind k);
  vecToVector: forall {k: Kind} {s: nat}, vec k s -> Vector.t (denoteKind k) s;
  vecToVector1: forall {s: nat}, vec Bit s -> Vector.t bit s;
  vecToVector2: forall {s: nat} (k2: Kind) (s2: nat), vec (BitVec k2 s2) s -> Vector.t (vec k2 s2) s;
  defaultKind: forall {k: Kind}, @denoteKind k;
  defaultBitVec : forall {sz}, vec Bit sz;          
  (* Constant values. *)
  zero : m bit; (* This component always returns the value 0. *)
  one : m bit; (* This component always returns the value 1. *)
  delayBit : bit -> m bit; (* Cava bit-level unit delay. *)
  loopBit : forall {A B : Type}, ((A * bit)%type -> m (B * bit)%type) -> A -> m B;
  (* Primitive gates *)
  inv : bit -> m bit;
  and2 : bit * bit -> m bit;
  nand2 : bit * bit -> m bit;
  or2 : bit * bit -> m bit;
  nor2 : bit * bit -> m bit;
  xor2 : bit * bit -> m bit;
  xnor2 : bit * bit -> m bit;
  buf_gate : bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'buf' *)
  (* Xilinx UNISIM FPGA gates *)
  lut1 : (bool -> bool) -> bit -> m bit; (* 1-input LUT *)
  lut2 : (bool -> bool -> bool) -> (bit * bit) -> m bit; (* 2-input LUT *)
  lut3 : (bool -> bool -> bool -> bool) -> (bit * bit * bit) -> m bit; (* 3-input LUT *)
  lut4 : (bool -> bool -> bool -> bool -> bool) -> (bit * bit * bit * bit) ->
         m bit; (* 4-input LUT *)
  lut5 : (bool -> bool -> bool -> bool -> bool -> bool) ->
         (bit * bit * bit * bit * bit) -> m bit; (* 5-input LUT *)
  lut6 : (bool -> bool -> bool -> bool -> bool -> bool -> bool) ->
         (bit * bit * bit * bit * bit * bit) -> m bit; (* 6-input LUT *)
  xorcy : bit * bit -> m bit; (* Xilinx fast-carry UNISIM with arguments O, CI, LI *)
  muxcy : bit -> bit -> bit -> m bit; (* Xilinx fast-carry UNISIM with arguments O, CI, DI, S *)
  (* Indexing is currently represented as a "circuit" but we may add features
     to the SystemVerilog netlist generation back-end to allow these to me
     functions rather than values in the monad type `m`.
  *)
  (* Dynamic indexing *)                                   
  indexAt : forall {k: Kind} {sz isz: nat}, vec k sz -> vec Bit isz -> denoteKind k;
  indexBitAt : forall {sz isz: nat}, vec Bit sz ->
                                     vec Bit isz -> bit;
  (* Static indexing *)
  indexConst : forall {k: Kind} {sz: nat}, vec k sz -> nat -> denoteKind k;
  indexBitConst : forall {sz: nat}, vec Bit sz -> nat -> bit;
  slice : forall {k: Kind} {sz: nat} (startAt len: nat), vec k sz ->
                 (startAt + len <= sz) -> vec k len;
  (* Synthesizable arithmetic operations. *)
  unsignedAdd : forall {a b : nat}, vec Bit a -> vec Bit b -> m (vec Bit (1 + max a b));
  addNN : forall {a : nat}, vec Bit a -> vec Bit a -> m (vec Bit a);
}.
