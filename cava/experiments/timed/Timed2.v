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

(** Experiments with timed proofs *)
Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Numbers.BinNums.
From Coq Require Import ZArith.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Require Export ExtLib.Data.Monads.StateMonad.
Require Export ExtLib.Data.Monads.WriterMonad.
Require Export ExtLib.Data.List.
Require Import ExtLib.Data.PPair.
Export MonadNotation.
Open Scope monad_scope.

Generalizable All Variables.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(* reduced Cava for experimentation*)
Class Cava m bit `{Monad m} := {
  delay_gate : bit -> m bit;
  not_gate : bit -> m bit;
  and_gate : list bit -> m bit;
}.

Notation Bit := bool.
Section Netlist.
  Variable Port : Type.

  Definition Ports := (list Port).
  Definition PortVal := (Port * Bit)%type.
  Definition PortsVal := (list PortVal).
  Definition NamedPorts := (list (string * Port))%type.
  
  Inductive Primitive : Type :=
  | Not  : Port -> Port -> Primitive
  | And  : list Port -> Port -> Primitive
  | Delay : Port -> Port -> Primitive.

  Inductive NetModule : Type :=  mkModule {
    moduleName : string;
    instances : list Primitive;
    inputs : Ports;
    outputs : Ports;
    names : NamedPorts;
  }.

  Definition addPrim (module : NetModule) (instance : Primitive): NetModule :=
  mkModule (moduleName module) (instance :: instances module) (inputs module) (outputs module) (names module).
End Netlist.

Section NetlistBuilder.
  Definition NetlistBuilder (T : Type) : Type := 
    state (nat * NetModule nat) T.

  Instance Monad_NetlistBuilder : Monad NetlistBuilder  :=
    Monad_state _.

  Instance State_NetlistBuilder : MonadState (nat * NetModule nat) NetlistBuilder :=
    MonadState_state _.

  Definition andNet (args : list nat): NetlistBuilder nat :=
    '(i, module) <- get ;;
    put ((i+1), addPrim nat module (And nat args i)) ;;
    ret i.

  Definition notNet (arg : nat): NetlistBuilder nat :=
    '(i, module) <- get ;;
    put ((i+1), addPrim nat module (Not nat arg i)) ;;
    ret i.

  Definition delayNet (arg : nat): NetlistBuilder nat :=
    '(i, module) <- get ;;
    put ((i+1), addPrim nat module (Delay nat arg i)) ;;
    ret i.

  Definition makeModule {t} (name : string) (n : NetlistBuilder t) : NetModule nat :=
  snd (execState n (0, mkModule nat name [] [] [] [])).
End NetlistBuilder.

Section NaiveStep.
  Fixpoint findPort (p: nat) (ps: PortsVal nat) :=
    match ps with
    | x :: xs => if beq_nat p (fst x)
                then Some (snd x)
                else findPort p xs
    | nil => None
    end.

  Fixpoint stepDelays (prims : lprimst (Primitive nat)) (last : PortsVal nat): PortsVal nat :=
    match prims with
    | Delay _ i o :: prims' => match findPort i last with
                | Some y => (o, y)
                | None => (o, false)
                end :: stepDelays prims' last
    | _ :: prims' => stepDelays prims' last
    | nil => nil
    end.

  (* Definition step (module : NetModule nat) (last : PortsT nat Bit): PortsT nat Bit := *)
End NaiveStep.

Definition nand2 {m t} `{Cava m t} := and_gate >=> not_gate.

Definition xor {m t} `{Cava m t} a b := 
  nab <- nand2 [a; b];;
  bn <- nand2 [b; nab];;
  an <- nand2 [a; nab];;
  ret (nand2 [an; bn]).

Definition xorDelayed {m t} `{Cava m t} a b := 
  nab <- nand2 [a; b] >>= delay_gate;;
  a' <- delay_gate a;;
  b' <- delay_gate b;;
  bn <- nand2 [b'; nab];;
  an <- nand2 [a'; nab];;
  ret (nand2 [an; bn] >>= delay_gate).