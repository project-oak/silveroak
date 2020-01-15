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
   Coq for the specification, implementaiton and formal verification of
   circuits. Experimental work, very much in flux, as Satnam learns Coq!
*)

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.
Import ListNotations.

Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.State.

Require Import Cava.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(******************************************************************************)
(* Build an inverter using only NAND gates.                                   *)
(******************************************************************************)

Definition inverter {m t} `{Cava m t} a := nand_gate [a; a].

Definition inverterTop {m t} `{CavaTop m t} :=
  setModuleName "invertor" ;;
  a <- input "a" ;
  b <- inverter a ;
  output "b" b.

Definition inverterNetlist := makeNetlist inverterTop.

(* A proof that the NAND-gate based implementation of the inverter is correct. *)
Lemma inverter_behaviour : forall (a : bool),
                           combinational (inverter a) = negb a.
Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  rewrite andb_diag.
  reflexivity.
Qed.

(******************************************************************************)
(* Build an AND-gate using only NAND gates.                                   *)
(******************************************************************************)

Definition andgate {m t} `{Cava m t} := nand_gate >=> not_gate.

Definition andgateTop {m t} `{CavaTop m t} :=
  setModuleName "andgate" ;;
  a <- input "a" ;
  b <- input "b" ;
  c <- andgate [a; b] ;
  output "c" c.

Definition andgateNetlist := makeNetlist andgateTop.

(* A proof that the NAND-gate based implementation of the AND-gate is correct. *)
Lemma andgate_behaviour : forall (a : bool) (b : bool),
                          combinational (andgate [a; b]) = a && b.
Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  rewrite negb_involutive.
  reflexivity.
Qed.

(******************************************************************************)
(* Build an OR-gate using only NAND gates.                                    *)
(******************************************************************************)

Definition orgate {m t} `{Cava m t} a b :=
  nota <- inverter a;
  notb <- inverter b;
  c <- nand_gate [nota; notb];
  return_ c.

Definition orgateTop {m t} `{CavaTop m t} :=
  setModuleName "orgate" ;;
  a <- input "a" ;
  b <- input "b" ;
  c <- orgate a b ;
  output "c" c.

Definition orgateNetlist := makeNetlist orgateTop.

(* A proof that the NAND-gate based implementation of the AND-gate is correct. *)
Lemma orgate_behaviour : forall (a : bool) (b : bool),
                         combinational (orgate a b) = a || b.
Proof.
  auto.
  intros.
  unfold combinational.
  unfold fst. 
  simpl.
  rewrite andb_diag.
  rewrite andb_diag.
  rewrite negb_andb.
  rewrite negb_involutive.
  rewrite negb_involutive.
  reflexivity.
Qed.
