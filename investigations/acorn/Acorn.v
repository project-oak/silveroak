(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.MonadState.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.

Inductive SignalType :=
  | Bit : SignalType 
  | Nat : SignalType.

Class Acorn (signal : SignalType -> Type) := {
  acorn : Type -> Type;
  monad :> Monad acorn;
  inv : signal Bit -> acorn (signal Bit);
  and2 : signal Bit * signal Bit -> acorn (signal Bit);
  addMod : nat -> signal Nat * signal Nat -> acorn (signal Nat);
}.

Inductive Instance :=
| Inv : N -> N -> N -> Instance
| And2 : N -> N -> N -> N -> Instance
| AddMod : N -> nat -> N -> N -> N -> Instance
| InputBit : string -> N -> Instance
| OutputBit : N -> string -> Instance
| InputNet : string -> N -> Instance
| OutputNet : N -> string -> Instance.

Record Netlist := mkNetlist {
  netlistName : string;
  instCount : N;
  bitCount : N;
  natCount : N;
  instances : list Instance;
}.

Definition emptyNetist : Netlist :=
  mkNetlist "" 0 0 0 [].

Inductive Signal : SignalType -> Type :=
| BitNet : N -> Signal Bit
| NatNet : N -> Signal Nat.

Definition denoteSignal (t: SignalType) : Type := Signal t.

Definition newWire : state Netlist (Signal Bit) :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is =>
      put (mkNetlist name ic (bc + 1) nc is) ;;
      ret (BitNet bc)
  end.

Definition newNat : state Netlist (Signal Nat) :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is =>
      put (mkNetlist name ic bc (nc + 1) is) ;;
      ret (NatNet nc)
  end.

Definition newInstNr : state Netlist N :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is =>
      put (mkNetlist name (ic + 1) bc nc is) ;;
      ret ic
  end.

Definition addInstance (inst : Instance) : state Netlist unit :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is =>
      put (mkNetlist name ic bc nc (inst::is))
  end.

Definition wireNr (w : Signal Bit) : N :=
  match w with
  | BitNet n => n
  end.

Definition invGate (i : Signal Bit) : state Netlist (Signal Bit) :=
  o <- newWire ;;
  instNr <- newInstNr ;;
  addInstance (Inv instNr (wireNr i) (wireNr o)) ;;
  ret o.
  
Definition and2Gate (i0i1 : Signal Bit * Signal Bit) : state Netlist (Signal Bit) :=
  o <- newWire ;;
  instNr <- newInstNr ;;
  let (i0, i1) := i0i1 in
  addInstance (And2 instNr (wireNr i0) (wireNr i1) (wireNr o)) ;;
  ret o.

Definition natWireNr (w : Signal Nat) : N :=
  match w with
  | NatNet n => n
  end.

Definition addModCircuit (modBy : nat) (i0i1 : Signal Nat * Signal Nat) : state Netlist (Signal Nat) :=
  o <- newNat ;;
  instNr <- newInstNr ;;
  let (i0, i1) := i0i1 in
  addInstance (AddMod instNr modBy (natWireNr i0) (natWireNr i1) (natWireNr o)) ;;
  ret o.

Instance AcornNetlist : Acorn denoteSignal := {
  acorn := state Netlist;
  monad := Monad_state _;
  inv := invGate;
  and2 := and2Gate;
  addMod := addModCircuit;
}.

Definition inputBit (name : string) : state Netlist (Signal Bit) :=
  o <- newWire ;;
  addInstance (InputBit name (wireNr o)) ;;
  ret o.

Definition outputBit (driver : Signal Bit) (name : string) : state Netlist unit :=
  addInstance (OutputBit (wireNr driver) name).

Definition nandGate : state Netlist unit :=
  i0 <- inputBit "i0" ;;
  i1 <- inputBit "i1" ;;
  o1 <- and2 (i0, i1) ;;
  o <- inv o1 ;;
  outputBit o "o".

Definition setCircuitName (name : string) : state Netlist unit :=
  ns <- get ;;
  match ns with
  | mkNetlist _ ic bc nc is =>
      put (mkNetlist name ic bc (nc + 1) is)
  end.

Definition netlist (name : string) (circuit : state Netlist unit) : Netlist :=
  execState (setCircuitName name ;; circuit) emptyNetist.

Compute netlist "nandGate" nandGate.

Local Open Scope string_scope.

Definition systemVerilog (nl : Netlist) : list string :=
  ["module " ++ netlistName nl ++ "();";
   "endmodule"].

Compute (systemVerilog (netlist "nandGate" nandGate)).

Fixpoint unlines (lines : list string) : string :=
  match lines with
  | [] => ""
  | x::xs => x ++ "\n" ++ unlines xs
  end.

Redirect "nandgate.sv" Eval compute in (unlines (systemVerilog (netlist "nandGate" nandGate))).
