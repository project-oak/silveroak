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
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Numbers.BinNums.
From Coq Require Import ZArith.
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadFix.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Export ExtLib.Data.Monads.StateMonad.
Export MonadNotation.

Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.

Generalizable All Variables.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* The Cava class represents circuit graphs with Coq-level inputs and
   outputs, but does not represent the IO ports of circuits. This allows
   us to define both circuit netlist interpretations for the Cava class
   as well as behavioural interpretations for attributing semantics. *)
Class Cava m bit `{Monad m} := {
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
  xorcy : bit * bit -> m bit; (* Xilinx fast-carry UNISIM with arguments O, CI, LI *)
  muxcy : bit -> bit -> bit -> m bit; (* Xilinx fast-carry UNISIM with arguments O, CI, DI, S *)
  (* Synthesizable arithmetic operations. *)
  unsignedAdd : nat -> list bit -> list bit -> m (list bit);
}.

(******************************************************************************)
(* Execute a monadic circuit description and return the generated netlist.    *)
(******************************************************************************)

Definition makeNetlist {t} (circuit : state CavaState t) : CavaState
  := execState circuit initState.

(******************************************************************************)
(* Netlist implementations for the Cava class.                                *)
(******************************************************************************)

Definition invNet (i : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindNot i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition andNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindAnd [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition nandNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindNand [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition orNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindOr [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition norNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindNor [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition xorNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindXor [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.


Definition xorcyNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindXorcy i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition xnorNet (i : N * N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindXnor [fst i; snd i] o) insts) inputs outputs )) ;;
         ret o
  end.

Definition bufNet (i : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindBuf i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition muxcyNet (s : N)  (di : N) (ci : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name (cons (BindMuxcy (s,(di,ci)) o) insts) inputs outputs )) ;;
         ret o
  end.

Definition unsignedAddNet (sumSize : nat)
                          (a : list N) (b : list N) :
                          state CavaState (list N) :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => let outv := map N.of_nat (seq (N.to_nat o) sumSize) in
         put (mkCavaState (o + (N.of_nat sumSize)) isSeq (mkModule name (cons (BindUnsignedAdd sumSize (a, b) outv) insts) inputs outputs )) ;;
         ret outv
  end.

Definition delayBitNet (i : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) true (mkModule name (cons (BindDelayBit i o) insts) inputs outputs )) ;;
         ret o
  end.

Definition loopBitNet (A B : Type) (f : (A * N)%type -> state CavaState (B * N)%type) (a : A) : state CavaState B :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule name insts inputs outputs)
      => put (mkCavaState (o+1) isSeq (mkModule name insts inputs outputs)) ;;
         '(b, cOut) <- f (a, o) ;;
          cs2 <- get ;;
          match cs2 with
          | mkCavaState o2 isSeq (mkModule name insts inputs outputs)
              => put (mkCavaState (o2+1) isSeq (mkModule name (cons (BindAssignBit o cOut) insts) inputs outputs)) ;;
                 ret b
          end
  end.

(******************************************************************************)
(* Instantiate the Cava class for CavaNet which describes circuits without    *)
(* any top-level pins or other module-level data                              *)
(******************************************************************************)

Instance CavaNet : Cava (state CavaState) N :=
  { zero := ret 0%N;
    one := ret 1%N;
    delayBit := delayBitNet;
    loopBit a b := loopBitNet a b;
    inv := invNet;
    and2 := andNet;
    nand2 := nandNet;
    or2 := orNet;
    nor2 := norNet;
    xor2 := xorNet;
    xnor2 := xorNet;
    buf_gate := bufNet;
    xorcy := xorcyNet;
    muxcy := muxcyNet;
    unsignedAdd := unsignedAddNet;
}.

(******************************************************************************)
(* Define netlist functions used to specify top-level module behaviour.       *)
(******************************************************************************)

Definition setModuleName (name : string) : state CavaState unit :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule _ insts inputs outputs)
     => put (mkCavaState o isSeq (mkModule name insts inputs outputs))
  end.

Definition inputVectorTo0 (size : nat) (name : string) : state CavaState (list N) :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs)
     => let netNumbers := map N.of_nat (seq (N.to_nat o) size) in
        let newPort := mkPort name (One (BitVec [size])) netNumbers in
        put (mkCavaState (o + (N.of_nat size)) isSeq (mkModule n insts (cons newPort inputs) outputs)) ;;
        ret netNumbers
  end.

Definition inputBit (name : string) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs)
     => let newPort := mkPort name (One Bit) o in
        put (mkCavaState (o+1) isSeq (mkModule n insts (cons newPort inputs) outputs)) ;;
        ret o
  end.

Definition outputBit (name : string) (i : N) : state CavaState N :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs)
     => let newPort := mkPort name (One Bit) i in
        put (mkCavaState o isSeq (mkModule n insts inputs (cons newPort outputs))) ;;
        ret i
  end.

Definition outputVectorTo0 (size : nat) (v : list N) (name : string) : state CavaState (list N) :=
  cs <- get ;;
  match cs with
  | mkCavaState o isSeq (mkModule n insts inputs outputs)
     => let newPort := mkPort name (One (BitVec [size])) v in
        put (mkCavaState o isSeq (mkModule n insts inputs (cons newPort outputs))) ;;
        ret v
  end.

(******************************************************************************)
(* A second boolean combinational logic interpretaiob for the Cava class      *)
(******************************************************************************)

Definition notBool (i : bool) : ident bool :=
  ret (negb i).

Definition andBool (i : bool * bool) : ident bool :=
  let (a, b) := i in ret (a && b).

Definition nandBool (i : bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (a && b)).

Definition orBool (i : bool * bool) : ident bool :=
  let (a, b) := i in ret (a || b).

Definition norBool (i : bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (a || b)).

Definition xorBool (i : bool * bool) : ident bool :=
  let (a, b) := i in ret (xorb a b).

Definition xorcyBool (i : bool * bool) : ident bool :=
  let (ci, li) := i in ret (xorb ci li).

Definition xnorBool (i : bool * bool) : ident bool :=
  let (a, b) := i in ret (negb (xorb a b)).

Definition muxcyBool (s : bool) (di : bool) (ci : bool) : ident bool :=
  ret (match s with
       | false => di
       | true => ci
       end).

Local Open Scope N_scope.

Definition unsignedAddBool (sumSize : nat)
                           (a : list bool) (b : list bool) :
                           ident (list bool) :=
  let a := list_bits_to_nat a in
  let b : N := list_bits_to_nat b in
  let sum := (a + b) mod 2^(N.of_nat sumSize) in
  ret (nat_to_list_bits_sized sumSize sum).

Local Open Scope N_scope.

Definition bufBool (i : bool) : ident bool :=
  ret i.

Definition loopBitBool (A B : Type) (f : A * bool -> ident (B * bool)) (a : A) : ident B :=
  '(b, _) <- f (a, false) ;;
  ret b.

(******************************************************************************)
(* Instantiate the Cava class for a boolean combinational logic               *)
(* interpretation.                                                            *)
(******************************************************************************)

Instance CavaBool : Cava ident bool :=
  { zero := ret false;
    one := ret true;
    delayBit i := ret i; (* Dummy definition for delayBit for now. *)
    loopBit a b := loopBitBool a b;
    inv := notBool;
    and2 := andBool;
    nand2 := nandBool;
    or2 := orBool;
    nor2 := norBool;
    xor2 := xorBool;
    xorcy := xorcyBool;
    xnor2 := xnorBool;
    muxcy := muxcyBool;
    unsignedAdd m n := @unsignedAddBool m n;
    buf_gate := bufBool;
}.

(******************************************************************************)
(* A function to run a monadic circuit description and return the boolean     *)
(* behavioural simulation result.                                             *)
(******************************************************************************)

Definition combinational {a} (circuit : ident a) : a := unIdent circuit.

(******************************************************************************)
(* A list-based sequential logic interpretaion for the Cava class      *)
(******************************************************************************)

Definition notBoolList (i : list bool) : ident (list bool) :=
  ret (map negb i).

Definition andBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in a && b) (combine (fst i) (snd i))).

Definition nandBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in negb (a && b)) (combine (fst i) (snd i))).

Definition orBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in a || b) (combine (fst i) (snd i))).

Definition norBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in negb (a || b)) (combine (fst i) (snd i))).

Definition xorBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in xorb a b) (combine (fst i) (snd i))).

Definition xorcyBoolList := xorBoolList.

Definition xnorBoolList (i : (list bool) * (list bool)) : ident (list bool) :=
  ret (map (fun (i : bool * bool) => let (a, b) := i in negb (xorb a b)) (combine (fst i) (snd i))).

Definition muxcyBoolList (s : list bool) (di : list bool) (ci : list bool) : ident (list bool) :=
  let dici := combine di ci in
  let s_dici := combine s dici in
  ret (map (fun (i : bool * (bool * bool)) =>
     let '(s, (ci, di)) := i in
     match s with
       | false => di
       | true => ci
     end) s_dici).

(* A dummy definition for unsignedAdd because I expect us to totally overhaul how
   we model sequential circuits.
   TODO(satnam): Replace with actual definition when sequential circuit semantics are clearer.
*)
Definition unsignedAddBoolList (sumSize : nat)
                               (a : list (list bool)) (b : list (list bool)) :
                               ident (list (list bool)) :=
  ret ([]).

Definition bufBoolList (i : list bool) : ident (list bool) :=
  ret i.

Definition loopBitBoolList (A B : Type) (f : A * list bool -> ident (B * list bool)) (a : A) : ident B :=
  '(b, _) <- f (a, [false]) ;;
  ret b.

Definition delayBitBoolList (i : list bool) : ident (list bool) :=
  ret (false :: i).

Instance CavaBoolList : Cava ident (list bool) :=
  { zero := ret [false];
    one := ret [true];
    delayBit := delayBitBoolList;
    loopBit := loopBitBoolList;
    inv := notBoolList;
    and2 := andBoolList;
    nand2 := nandBoolList;
    or2 := orBoolList;
    nor2 := norBoolList;
    xor2 := xorBoolList;
    xorcy := xorcyBoolList;
    xnor2 := xnorBoolList;
    muxcy := muxcyBoolList;
    unsignedAdd := unsignedAddBoolList;
    buf_gate := bufBoolList;
}.

Definition sequential {a} (circuit : ident (list a)) : list a := unIdent circuit.

