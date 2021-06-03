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
Require Import Coq.Strings.Ascii.
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
| AddMod : nat -> N -> N -> N -> Instance.

Inductive Port :=
| InputBit : string -> N -> Port
| OutputBit : N -> string -> Port
| InputNat : string -> N -> Port
| OutputNat : N -> string -> Port.

Record Netlist := mkNetlist {
  netlistName : string;
  instCount : N;
  bitCount : N;
  natCount : N;
  instances : list Instance;
  ports : list Port;
}.

Definition emptyNetist : Netlist :=
  mkNetlist "" 0 0 0 [] [].

Inductive Signal : SignalType -> Type :=
| BitNet : N -> Signal Bit
| NatNet : N -> Signal Nat.

Definition denoteSignal (t: SignalType) : Type := Signal t.

Definition newWire : state Netlist (Signal Bit) :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic (bc + 1) nc is ps) ;;
      ret (BitNet bc)
  end.

Definition newNat : state Netlist (Signal Nat) :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc (nc + 1) is ps) ;;
      ret (NatNet nc)
  end.

Definition newInstNr : state Netlist N :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name (ic + 1) bc nc is ps) ;;
      ret ic
  end.

Definition addInstance (inst : Instance) : state Netlist unit :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc nc (inst::is) ps)
  end.

Definition addPort (p : Port) : state Netlist unit :=
  ns <- get ;;
  match ns with
  | mkNetlist name ic bc nc is ps =>
      put (mkNetlist name ic bc nc is (p::ps))
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
  let (i0, i1) := i0i1 in
  addInstance (AddMod modBy (natWireNr i0) (natWireNr i1) (natWireNr o)) ;;
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
  addPort (InputBit name (wireNr o)) ;;
  ret o.

Definition outputBit (driver : Signal Bit) (name : string) : state Netlist unit :=
  addPort (OutputBit (wireNr driver) name).

Definition inputNat (name : string) : state Netlist (Signal Nat) :=
  o <- newNat ;;
  addPort (InputNat name (natWireNr o)) ;;
  ret o.

Definition outputNat (driver : Signal Nat) (name : string) : state Netlist unit :=
  addPort (OutputNat (natWireNr driver) name).

Definition setCircuitName (name : string) : state Netlist unit :=
  ns <- get ;;
  match ns with
  | mkNetlist _ ic bc nc is ps =>
      put (mkNetlist name ic bc nc is ps)
  end.

Definition netlist (name : string) (circuit : state Netlist unit) : Netlist :=
  execState (setCircuitName name ;; circuit) emptyNetist.

Local Open Scope string_scope.

Fixpoint insertCommas (lines : list string) : string :=
  match lines with
  | [] => ""
  | [x] => x
  | x::xs => x ++ ", " ++ insertCommas xs
  end.

Definition portDeclaration (p : Port) : string :=
  match p with
  | InputBit name _ => "input logic " ++ name
  | OutputBit _ name => "output logic " ++ name
  | InputNat name _ => "input int unsigned " ++ name
  | OutputNat _ name => "output int unsigned " ++ name
  end.

Definition portDeclarations := map portDeclaration.

Open Scope char_scope.
Open Scope N_scope.

Definition NToDigit (n : N) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Fixpoint showNAux (time : nat) (n : N) (acc : string) : string :=
  let acc' := String (NToDigit (n mod 10)) acc in
  match time with
    | 0%nat => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => showNAux time' n' acc'
      end
  end.

Open Scope string_scope.

Definition showN (n : N) : string :=
  showNAux (N.to_nat n) n "".

Definition declareBitNets (bc : N) : list string :=
  match bc with
  | N0 => []
  | Npos bc' => ["  logic net[0:" ++ showN (bc - 1) ++ "];"]
  end.

Definition declareNatNets (nc : N) : list string :=
  match nc with
  | N0 => []
  | Npos nc' => ["  logic nat[0:" ++ showN (nc - 1) ++ "];"]
  end.

Definition declareLocalNets (nl : Netlist) : list string :=
  declareBitNets (bitCount nl) ++ declareNatNets (natCount nl).

Definition netS (n : N) : string := "net[" ++ showN n ++ "]".

Definition natS (n : N) : string := "nat[" ++ showN n ++ "]".


Definition instantiateComponent (component : Instance) : string :=
  match component with
  | Inv instNr i o => "  not not_" ++ showN instNr ++ " (" ++
                      netS i ++ ", " ++ netS o ++ ");"
  | And2 instNr i0 i1 o => "  and and_" ++ showN instNr ++ " (" ++ netS i0 ++ ", " ++  netS i1 ++
                          ", " ++ netS o ++ ");"
  | AddMod modVal i0 i1 o => "  assign " ++ natS o ++ " = (" ++ natS i0 ++ " + " ++
                             natS i1 ++ ") % " ++ showN (N.of_nat modVal) ++ ";"
  end.

Definition instantiateComponents := map instantiateComponent.
  

Definition systemVerilogLines (nl : Netlist) : list string :=
  ["module " ++ netlistName nl ++ " (" ++ insertCommas (portDeclarations (ports nl)) ++ ");"] ++
  declareLocalNets nl ++
  instantiateComponents (instances nl) ++
  ["endmodule"].

Fixpoint unlines (lines : list string) : string :=
  match lines with
  | [] => ""
  | x::xs => x ++ "\n" ++ unlines xs
  end.

Definition systemVerilog (name : string) (nl : state Netlist unit ) : string :=
  unlines (systemVerilogLines (netlist name nl)).

Definition nandGate : state Netlist unit :=
  i0 <- inputBit "i0" ;;
  i1 <- inputBit "i1" ;;
  o1 <- and2 (i0, i1) ;;
  o <- inv o1 ;;
  outputBit o "o".

Redirect "nandgate.sv" Eval compute in (systemVerilog "nandGate" nandGate).

Definition addmod : state Netlist unit :=
  a <- inputNat "a" ;;
  b <- inputNat "b" ;;
  c <- addMod 6 (a, b) ;;
  outputNat c "c".

Redirect "addmod.sv" Eval compute in (systemVerilog "addmod" addmod).