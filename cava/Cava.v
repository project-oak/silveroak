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
From Coq Require Numbers.BinNums.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.

Generalizable All Variables.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(******************************************************************************)
(* Primitive elements                                                         *)
(******************************************************************************)

(* The primitive elements that can be instantiated in Cava. Some are generic
   SystemVerilog gates that can be used with synthesis and back-end tools to
   map to any architecture, while others are specific to Xilinx FPGAs.
*)

Inductive Primitive :=
  (* SystemVerilog primitive gates. *)
  | Not  : Z -> Z -> Primitive
  | And  : list Z -> Z -> Primitive
  | Nand : list Z -> Z -> Primitive
  | Or   : list Z -> Z -> Primitive
  | Nor  : list Z -> Z -> Primitive
  | Xor  : list Z -> Z -> Primitive
  | Xnor : list Z -> Z -> Primitive
  | Buf  : Z -> Z -> Primitive
  (* A Cava unit delay bit component. *)
  | DelayBit : Z -> Z -> Primitive
  (* Xilinx FPGA architecture specific gates. *)
  | Xorcy : Z -> Z -> Z -> Primitive
  | Muxcy : Z -> Z -> Z -> Z -> Primitive.

(* The Cava class represents circuit graphs with Coq-level inputs and
   outputs, but does not represent the IO ports of circuits. This allows
   us to define both circuit netlist interpretations for the Cava class
   as well as behavioural interpretations for attributing semantics. *)
Class Cava m bit `{Monad m} := {
  (* Constant values. *)
  zero : m bit; (* This component always returns the value 0. *)
  one : m bit; (* This component always returns the value 1. *)
  delayBit : bit -> m bit; (* Cava bit-level unit delay. *)
  (* Primitive SystemVerilog gates *)
  not_gate : bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'not' *)
  and_gate : list bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'and' *)
  nand_gate : list bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'nand' *)
  or_gate : list bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'or' *)
  nor_gate : list bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'nor' *)
  xor_gate : list bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'xor' *)
  xnor_gate : list bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'xnor' *)
  buf_gate : bit -> m bit; (* Corresponds to the SystemVerilog primitive gate 'buf' *)
  (* Xilinx UNISIM FPGA gates *)
  xorcy : bit -> bit -> m bit; (* Xilinx fast-carry UNISIM with arguments O, CI, LI *)
  muxcy : bit -> bit -> bit -> m bit; (* Xilinx fast-carry UNISIM with arguments O, CI, DI, S *)
}.

(******************************************************************************)
(* Data structures to represent circuit graph/netlist state                   *)
(******************************************************************************)

Record Instance : Type := mkInstance {
  inst_number : Z;
  instance : Primitive ;
}.

Inductive PortType :=
  | BitPort : Z -> PortType
  | VectorTo0Port : list Z -> PortType
  | VectorFrom0Port : list Z -> PortType.

Record PortDeclaration : Type := mkPort {
  port_name : string;
  port_type : PortType;
}.

Record CavaState : Type := mkCavaState {
  moduleName : string;
  netNumber : Z;
  instances : list Instance;
  inputs : list PortDeclaration;
  outputs : list PortDeclaration;
  isSequential : bool;
}.

(******************************************************************************)
(* The initial empty netlist                                                  *)
(******************************************************************************)

(* Net number 0 carries the constant signal zero. Net number 1 carries the
   constant signal 1. We start numbering from 2 for the user nets.
*) 

Definition initState : CavaState
  := mkCavaState "" 2 [] [] [] false.

(******************************************************************************)
(* Execute a monadic circuit description and return the generated netlist.    *)
(******************************************************************************)

Definition makeNetlist {t} (circuit : State CavaState t)
  := snd (circuit initState).

(******************************************************************************)
(* Netlist implementations for the Cava class.                                *)
(******************************************************************************)

Definition notNet (i : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Not i o)) insts) inputs outputs isSeq) ;;
         return_ o
  end. 

Definition andNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (And i o)) insts) inputs outputs isSeq) ;;
         return_ o
  end.

Definition nandNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Nand i o)) insts) inputs outputs isSeq) ;;
         return_ o
  end.

Definition orNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Or i o)) insts) inputs outputs isSeq) ;;
         return_ o
  end.

Definition norNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Nor i o)) insts) inputs outputs isSeq) ;;
         return_ o
  end.

Definition xorNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Xor i o)) insts) inputs outputs isSeq) ;;
         return_ o
  end.


Definition xorcyNet (ci : Z) (li : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Xorcy ci li o)) insts) inputs outputs isSeq) ;;
         return_ o
  end.

Definition xnorNet (i : list Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Xnor i o)) insts) inputs outputs isSeq) ;;
         return_ o
  end.

Definition bufNet (i : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Buf i o)) insts) inputs outputs isSeq) ;;
         return_ o
  end. 

Definition muxcyNet (s : Z)  (di : Z) (ci : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs isSeq
      => put (mkCavaState name (o+1) (cons (mkInstance o (Muxcy s di ci o)) insts) inputs outputs isSeq) ;;
         return_ o
  end.

Definition delayBitNet (i : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState name o insts inputs outputs _
      => put (mkCavaState name (o+1) (cons (mkInstance o (DelayBit i o)) insts) inputs outputs true) ;;
         return_ o
  end. 

(******************************************************************************)
(* Instantiate the Cava class for CavaNet which describes circuits without    *)
(* any top-level pins or other module-level data                              *)
(******************************************************************************)

Instance CavaNet : Cava (State CavaState) Z :=
  { zero := return_ 0%Z;
    one := return_ 1%Z;
    delayBit := delayBitNet;
    not_gate := notNet;
    and_gate := andNet;
    nand_gate := nandNet;
    or_gate := orNet;
    nor_gate := norNet;
    xor_gate := xorNet;
    xorcy := xorcyNet;
    xnor_gate := xnorNet;
    muxcy := muxcyNet;
    buf_gate := bufNet;
}.

(******************************************************************************)
(* Define netlist functions used to specify top-level module behaviour.       *)
(******************************************************************************)

Definition setModuleNameNet (name : string) : State CavaState unit :=
  cs <- get;
  match cs with
  | mkCavaState _ o insts inputs outputs isSeq
     => put (mkCavaState name o insts inputs outputs isSeq)
  end.

Definition inputVectorTo0Net (size : Z) (name : string)  : State CavaState (list Z) := 
  cs <- get;
  match cs with
  | mkCavaState n o insts inputs outputs isSeq
     => let netNumbers := map Z.of_nat (seq (Z.abs_nat o) (Z.abs_nat size)) in
        let newPort := mkPort name (VectorTo0Port netNumbers) in
        put (mkCavaState n (o + size) insts (cons newPort inputs) outputs isSeq) ;;
        return_ netNumbers
  end.

Definition inputBitNet (name : string) : State CavaState Z := 
  cs <- get;
  match cs with
  | mkCavaState n o insts inputs outputs isSeq
     => let newPort := mkPort name (BitPort o) in
        put (mkCavaState n (o+1) insts (cons newPort inputs) outputs isSeq) ;;
        return_ o
  end.

Definition outputBitNet (name : string) (i : Z) : State CavaState Z :=
  cs <- get;
  match cs with
  | mkCavaState n o insts inputs outputs isSeq
     => let newPort := mkPort name (BitPort i) in
        put (mkCavaState n o insts inputs (cons newPort outputs) isSeq) ;;
        return_ i
  end.

Definition outputVectorTo0Net (v : list Z) (name : string) : State CavaState (list Z) := 
  cs <- get;
  match cs with
  | mkCavaState n o insts inputs outputs isSeq
     => let newPort := mkPort name (VectorTo0Port v) in
        put (mkCavaState n o insts inputs (cons newPort outputs) isSeq) ;;
        return_ v
  end.


(******************************************************************************)
(* Instantiate the top-level Cava class for netlist behaviour.                *)
(******************************************************************************)

Class CavaTop m bit `{Cava m bit} := {
  (* Name to be used for the extracted VHDL/Verilog/SystemVerilog module *)
  setModuleName : string -> m unit;
  (* Input and output ports. *)
  inputBit : string -> m bit;            (* A one bit input. *)
  outputBit : string -> bit -> m bit;    (* A one bit output. *)
  inputVectorTo0 : Z -> string -> m (list bit);
  outputVectorTo0 : list bit -> string -> m (list bit);
}.

Instance CavaTopNet : CavaTop (State CavaState) Z :=
  { setModuleName := setModuleNameNet;
    inputBit := inputBitNet;
    outputBit := outputBitNet;
    inputVectorTo0 := inputVectorTo0Net;
    outputVectorTo0 := outputVectorTo0Net;
}.

(******************************************************************************)
(* A second boolean combinational logic interpretaiob for the Cava class      *)
(******************************************************************************)

Definition notBool (i : bool) : State unit bool :=
  return_ (negb i).

Definition andBool (i : list bool) : State unit bool :=
  return_ (fold_left (fun a b => a && b) i true).

Definition nandBool (i : list bool) : State unit bool :=
  return_ (negb (fold_left (fun a b => a && b) i true)).

Definition orBool (i : list bool) : State unit bool :=
  return_ (fold_left (fun a b => a || b) i false).

Definition norBool (i : list bool) : State unit bool :=
  return_ (negb (fold_left (fun a b =>  a || b) i true)).

Definition xorBool (i : list bool) : State unit bool :=
  return_ (fold_left (fun a b => xorb a b) i false).

Definition xorcyBool (li : bool) (ci : bool) : State unit bool :=
  return_ (xorb ci li).

Definition xnorBool (i : list bool) : State unit bool :=
  return_ (negb (fold_left (fun a b => xorb a b) i false)).

Definition muxcyBool (s : bool) (di : bool) (ci : bool)  : State unit bool :=
  return_ (match s with
           | false => di
           | true => ci
           end).

Definition bufBool (i : bool) : State unit bool :=
  return_ i.

Definition inputBool (name : string) : State unit bool :=
  return_ false.

Definition outputBool (name : string) (i : bool) : State unit bool :=
  return_ i.

(******************************************************************************)
(* Instantiate the Cava class for a boolean combinational logic               *)
(* interpretation.                                                            *)
(******************************************************************************)

Instance CavaBool : Cava (State unit) bool :=
  { zero := return_ false;
    one := return_ true;
    delayBit i := return_ i; (* Dummy definition for delayBit for now. *)
    not_gate := notBool;
    and_gate := andBool;
    nand_gate := nandBool;
    or_gate := orBool;
    nor_gate := norBool;
    xor_gate := xorBool;
    xorcy := xorcyBool;
    xnor_gate := xnorBool;
    muxcy := muxcyBool;
    buf_gate := bufBool;
}.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition combinational {a} (circuit : State unit a) := fst (circuit tt).

(******************************************************************************)
(* Lava-style circuit combinators.                                            *)
(******************************************************************************)


(* Below combinator

-------------------------------------------------------------------------------
-- Below
-------------------------------------------------------------------------------
-- below r s
--            ^
--            |
--            f
--            ^
--            |
--          -----
--         |     |
--     c ->|  s  |-> e
--         |     |
--          -----
--            ^ 
--            |
--            g
--            ^
--            |
--          -----
--         |     |
--     b ->|  r  |-> d
--         |     |
--          -----
--            ^ 
--            |
--            a
-------------------------------------------------------------------------------
*)

Fixpoint below `{Monad m} {A B C D E F G}
             (r : A * B -> m (D * G)%type)
             (s : G * C -> m (E * F)%type)
             (abc : A * (B * C)) : m ((D * E) * F)%type :=
  let (a, bc) := abc in
  let (b, c) := bc in
  dg <- r (a, b) ;
  let (d, g) := dg : D * G in
  ef <- s (g, c) ;
  let (e, f) := ef : E * F in
  return_ ((d, e), f).

(* The col combinator takes a 4-sided circuit element and replicates it by
   composing each element in a chain.

-------------------------------------------------------------------------------
-- 4-Sided Tile Combinators 
-------------------------------------------------------------------------------
-- COL r
--            a
--            ^
--            |
--          -----
--         |     |
--     b ->|  r  |-> c
--         |     |
--          -----
--            ^
--            |
--            a
--            ^
--            |
--          -----
--         |     |
--     b ->|  r  |-> c
--         |     |
--          -----
--            ^ 
--            |
--            a
--            ^
--            |
--          -----
--         |     |
--     b ->|  r  |-> c
--         |     |
--          -----
--            ^ 
--            |
--            a
-------------------------------------------------------------------------------


*)

Fixpoint col `{Monad m} {A B C}
             (circuit : A * B -> m (C * A)%type) (a : A) (b : list B) :
             m (list C * A)%type :=
  match b with
  | [] => return_ ([], a)
  | b0::br => c_cs_e <- below circuit (fun ab => col circuit (fst ab) (snd ab)) (a, (b0, br)) ;
                   let (c_cs, e) := c_cs_e : (C * list C) * A in
                   let (c, cs) := c_cs : C * list C in
                   return_ (c::cs, e)
  end.

(******************************************************************************)
(* Loop combinator                                                            *)
(******************************************************************************)


(*

   ------------
  |    ----    |
  |-->|    |---  C (looped back)
      |    |
  A ->|    | -> B
       ----

It seems like I need a recursive-do style definition here to allow me to
use c in the result and as an argument to circuit.

Definition loop `{Monad m} {A B C}
                (circuit : A * C -> m (B * C)%type) : A -> m B :=
  fun (a : A) =>
    bc <- circuit (a, c) ;
    return_ (fst bc).

*)