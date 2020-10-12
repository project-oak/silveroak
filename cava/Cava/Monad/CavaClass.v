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
From Cava Require Import Types.

(* The Cava class represents circuit graphs with Coq-level inputs and
   outputs, but does not represent the IO ports of circuits. This allows
   us to define both circuit netlist interpretations for the Cava class
   as well as behavioural interpretations for attributing semantics. *)
Class Cava m `{Monad m} bit := {
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
  indexAt : forall {k: Kind} {sz isz: nat},
            Vector.t (smashTy bit k) sz -> Vector.t bit isz -> smashTy bit k;
  indexBitAt : forall {sz isz: nat}, Vector.t bit sz ->
                                     Vector.t bit isz -> bit;
  (* Static indexing *)
  indexConst : forall {k: Kind} {sz: nat},
               Vector.t (smashTy bit k) sz -> nat -> smashTy bit k;
  indexBitConst : forall {sz: nat}, Vector.t bit sz -> nat -> bit;
  slice : forall {k: Kind}  {sz: nat} (startAt len: nat),
                 Vector.t (smashTy bit k) sz ->
                 (startAt + len <= sz) -> Vector.t (smashTy bit k) len ;
  (* Synthesizable arithmetic operations. *)
  unsignedAdd : forall {a b : nat}, Vector.t bit a -> Vector.t bit b ->
                m (Vector.t bit (1 + max a b));
  (* Synthesizable relational operators *)
  greaterThanOrEqual : forall {a b : nat}, Vector.t bit a -> Vector.t bit b ->
                       m bit;
}.
