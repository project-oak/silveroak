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

Require Import ExtLib.Structures.Monad.
Require Import Cava.Netlist.
Require Import Cava.Signal.

Local Open Scope type_scope.

(* The Cava class represents circuit graphs with Coq-level inputs and
   outputs, but does not represent the IO ports of circuits. This allows
   us to define both circuit netlist interpretations for the Cava class
   as well as behavioural interpretations for attributing semantics. *)
Class Cava (signal : SignalType -> Type) := {
  cava : Type -> Type;
  monad :> Monad cava;
  (* Constant values. *)
  constant : bool -> signal Bit;
  (* Default values. *)
  defaultSignal : forall {t: SignalType}, signal t;
  (* SystemVerilog primitive gates *)
  inv : signal Bit -> cava (signal Bit);
  and2 : signal Bit * signal Bit -> cava (signal Bit);
  nand2 : signal Bit * signal Bit -> cava (signal Bit);
  or2 : signal Bit * signal Bit -> cava (signal Bit);
  nor2 : signal Bit * signal Bit -> cava (signal Bit);
  xor2 : signal Bit * signal Bit -> cava (signal Bit);
  xnor2 : signal Bit * signal Bit -> cava (signal Bit);
  buf_gate : signal Bit -> cava (signal Bit); (* Corresponds to the SystemVerilog primitive gate 'buf' *)
  (* Xilinx UNISIM FPGA gates *)
  lut1 : (bool -> bool) -> signal Bit -> cava (signal Bit); (* 1-input LUT *)
  lut2 : (bool -> bool -> bool) -> (signal Bit * signal Bit) -> cava (signal Bit); (* 2-input LUT *)
  lut3 : (bool -> bool -> bool -> bool) -> signal Bit * signal Bit * signal Bit -> cava (signal Bit); (* 3-input LUT *)
  lut4 : (bool -> bool -> bool -> bool -> bool) -> (signal Bit * signal Bit * signal Bit * signal Bit) ->
         cava (signal Bit); (* 4-input LUT *)
  lut5 : (bool -> bool -> bool -> bool -> bool -> bool) ->
         (signal Bit * signal Bit * signal Bit * signal Bit * signal Bit) -> cava (signal Bit); (* 5-input LUT *)
  lut6 : (bool -> bool -> bool -> bool -> bool -> bool -> bool) ->
         signal Bit * signal Bit * signal Bit * signal Bit * signal Bit * signal Bit -> cava (signal Bit); (* 6-input LUT *)
  xorcy : signal Bit * signal Bit -> cava (signal Bit); (* Xilinx fast-carry UNISIM with arguments O, CI, LI *)
  muxcy : signal Bit -> signal  Bit -> signal Bit -> cava (signal Bit); (* Xilinx fast-carry UNISIM with arguments O, CI, DI, S *)
  (* Converting to/from Vector.t *)
  unpackv : forall {t : SignalType} {s : nat}, signal (Vec t s) -> cava (Vector.t (signal t) s);
  packv : forall {t : SignalType} {s : nat} , Vector.t (signal t) s -> cava (signal (Vec t s));
  indexAt : forall {t : SignalType} {sz isz: nat},
            signal (Vec t sz) ->     (* A vector of n elements of type signal t *)
            signal (Vec Bit isz) ->  (* A bit-vector index of size isz bits *)
            cava (signal t);                (* The indexed value of type signal t *)
  (* Static indexing *)
  indexConst : forall {t: SignalType} {sz: nat},
               signal (Vec t sz) ->     (* A vector of n elements of type signal t *)
               nat ->                   (* Static index *)
               cava (signal t);                (* The indexed bit of type signal bit *)
  slice : forall {t: SignalType} {sz: nat} (startAt len: nat),
                 signal (Vec t sz) ->
                 (startAt + len <= sz) ->
                 cava (signal (Vec t len));
  (* Synthesizable arithmetic operations. *)
  unsignedAdd : forall {a b : nat}, signal (Vec Bit a) * signal (Vec Bit b) ->
                cava (signal (Vec Bit (1 + max a b)));
  unsignedMult : forall {a b : nat}, signal (Vec Bit a) * signal (Vec Bit b)->
                cava (signal (Vec Bit (a + b)));
  (* Synthesizable relational operators *)
  greaterThanOrEqual : forall {a b : nat}, signal (Vec Bit a) * signal (Vec Bit b) ->
                      cava (signal Bit);
  (* Naming for sharing. *)
  localSignal : forall {t : SignalType}, signal t -> cava (signal t);
  (* Hierarchy *)
  instantiate : forall (intf: CircuitInterface),
                 (tupleInterface signal (map port_type (circuitInputs intf)) ->
                  cava (tupleInterface signal (map port_type (circuitOutputs intf)))) ->
                 tupleInterface signal (map port_type (circuitInputs intf)) ->
                 cava (tupleInterface signal ((map port_type (circuitOutputs intf))));
  (* Instantiation of black-box components which return default values. *)
  blackBox : forall (intf: CircuitInterface),
             tupleInterface signal (map port_type (circuitInputs intf)) ->
             cava (tupleInterface signal ((map port_type (circuitOutputs intf))));
}.
