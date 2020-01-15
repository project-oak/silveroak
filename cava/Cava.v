(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
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
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.

Local Open Scope list_scope.
Local Open Scope monad_scope.

Set Printing Implicit.
Set Printing All.

(* The Cava class represents circuit graphs with Coq-level inputs and
   outputs, but does not represent the IO ports of circuits. This allows
   us to define both circuit netlist interpretations for the Cava class
   as well as behavioural interpretations for attributing semantics. *)
Class Cava m t `{Monad m} := {
  (* Primitive SystemVerilog gates *)
  not_gate : t -> m t; (* Corresponds to the SystemVerilog primitive gate 'not' *)
  and_gate : list t -> m t; (* Corresponds to the SystemVerilog primitive gate 'and' *)
  nand_gate : list t -> m t; (* Corresponds to the SystemVerilog primitive gate 'nand' *)
  or_gate : list t -> m t; (* Corresponds to the SystemVerilog primitive gate 'or' *)
  nor_gate : list t -> m t; (* Corresponds to the SystemVerilog primitive gate 'nor' *)
  xor_gate : list t -> m t; (* Corresponds to the SystemVerilog primitive gate 'xor' *)
  xnor_gate : list t -> m t; (* Corresponds to the SystemVerilog primitive gate 'xnor' *)
  buf_gate : t -> m t; (* Corresponds to the SystemVerilog primitive gate 'buf' *)
}.

Record Instance : Type := mkInstance {
  inst_name : string;
  inst_number : Z;
  inst_args : list Z;
}.

Record CavaState : Type := mkCavaState {
  moduleName : string;
  netNumber : Z;
  instances : list Instance;
  inputs : list (string * Z);
  outputs : list (string * Z);
}.

Definition initState : CavaState
  := mkCavaState "" 0 [] [] [].


Definition makeNetlist (circuit : State CavaState Z) := snd (circuit initState).

Definition notNet (i : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs
      => put (mkCavaState name (o+1) (cons (mkInstance "not" o [o; i]) insts) inputs outputs) ;;
         return_ o
  end. 

Definition andNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs
      => put (mkCavaState name (o+1) (cons (mkInstance "and" o (cons o i)) insts) inputs outputs) ;;
         return_ o
  end.

Definition nandNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs
      => put (mkCavaState name (o+1) (cons (mkInstance "nand" o (cons o i)) insts) inputs outputs) ;;
         return_ o
  end.

Definition orNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs
      => put (mkCavaState name (o+1) (cons (mkInstance "or" o (cons o i)) insts) inputs outputs) ;;
         return_ o
  end.

Definition norNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs
      => put (mkCavaState name (o+1) (cons (mkInstance "nor" o (cons o i)) insts) inputs outputs) ;;
         return_ o
  end.

Definition xorNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs
      => put (mkCavaState name (o+1) (cons (mkInstance "xor" o (cons o i)) insts) inputs outputs) ;;
         return_ o
  end.

Definition xnorNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs
      => put (mkCavaState name (o+1) (cons (mkInstance "nxor" o (cons o i)) insts) inputs outputs) ;;
         return_ o
  end.

Definition bufNet (i : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs
      => put (mkCavaState name (o+1) (cons (mkInstance "buf" o [o; i]) insts) inputs outputs) ;;
         return_ o
  end. 

Instance CavaNet : Cava (State CavaState) Z :=
  { not_gate := notNet;
    and_gate := andNet;
    nand_gate := nandNet;
    or_gate := orNet;
    nor_gate := norNet;
    xor_gate := xorNet;
    xnor_gate := xnorNet;
    buf_gate := bufNet;
}.

Definition setModuleNameNet (name : string) : State CavaState unit :=
  cs <- get;
  match cs with
  | mkCavaState _ o insts inputs outputs
     => put (mkCavaState name o insts inputs outputs)
  end.

Definition inputNet (name : string) : State CavaState Z := 
  cs <- get;
  match cs with
  | mkCavaState n o insts inputs outputs
     => put (mkCavaState n (o+1) insts (cons (name, o) inputs) outputs) ;;
        return_ o
  end.

Definition outputNet (name : string) (i : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState n o insts inputs outputs
     => put (mkCavaState n o insts inputs (cons (name, i) outputs)) ;;
        return_ i
  end.

Class CavaTop m t `{Cava m t} := {
  (* Name to be used for the extracted VHDL/Verilog/SystemVerilog module *)
  setModuleName : string -> m unit;
  (* Input and output ports. *)
  input : string -> m t;
  output : string -> t -> m t;
}.

Instance CavaTopNet : CavaTop (State CavaState) Z :=
  { setModuleName := setModuleNameNet;
    input := inputNet;
    output := outputNet;
}.

Definition notBool (i : bool) : State unit bool :=
  return_ (negb i).

Definition andBool (i : list bool) : State unit bool :=
  return_ (fold_left (fun a b => a && b) i true).

Definition nandBool (i : list bool) : State unit bool :=
  return_ (negb (fold_left (fun a b => a && b) i true)).

Definition orBool (i : list bool) : State unit bool :=
  return_ (fold_left (fun a b => a || b) i true).

Definition norBool (i : list bool) : State unit bool :=
  return_ (negb (fold_left (fun a b =>  a || b) i true)).

Definition xorBool (i : list bool) : State unit bool :=
  return_ (fold_left (fun a b => xorb a b) i true).

Definition xnorBool (i : list bool) : State unit bool :=
  return_ (negb (fold_left (fun a b => xorb a b) i true)).

Definition bufBool (i : bool) : State unit bool :=
  return_ i.

Definition inputBool (name : string) : State unit bool :=
  return_ false.

Definition outputBool (name : string) (i : bool) : State unit bool :=
  return_ i.

Instance CavaBool : Cava (State unit) bool :=
  { not_gate := notBool;
    and_gate := andBool;
    nand_gate := nandBool;
    or_gate := orBool;
    nor_gate := norBool;
    xor_gate := xorBool;
    xnor_gate := xnorBool;
    buf_gate := bufBool;
}.

Definition combinational (circuit : State unit bool) := fst (circuit tt).




