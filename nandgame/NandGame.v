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

(* Cava implementations of the gates described in the Nand Game website
   which describes how to build circuit components using only NAND gates
   and registers. http://nandgame.com/
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(******************************************************************************)
(* Build an inverter using only NAND gates.                                   *)
(******************************************************************************)

Definition inverter {m t} `{Cava m t} a := nand_gate [a; a].

Definition inverterTop :=
  setModuleName "invertor" ;;
  a <- inputBit "a" ;;
  b <- inverter a ;;
  outputBit "b" b.

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

Definition andgate {m t} `{Cava m t}  a b :=
  x <- nand_gate [a; b] ;;
  c <- inverter x ;;
  ret c.

Definition andgateTop :=
  setModuleName "andgate" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  c <- andgate a b ;;
  outputBit "c" c.

Definition andgateNetlist := makeNetlist andgateTop.

(* A proof that the NAND-gate based implementation of the AND-gate is correct. *)
Lemma andgate_behaviour : forall (a : bool) (b : bool),
                          combinational (andgate a b) = a && b.
Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  rewrite andb_diag.
  rewrite negb_involutive.
  reflexivity.
Qed.

(******************************************************************************)
(* Build an OR-gate using only NAND gates.                                    *)
(******************************************************************************)

Definition orgate {m t} `{Cava m t} a b :=
  nota <- inverter a ;;
  notb <- inverter b ;;
  c <- nand_gate [nota; notb] ;;
  ret c.

Definition orgateTop :=
  setModuleName "orgate" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  c <- orgate a b ;;
  outputBit "c" c.

Definition orgateNetlist := makeNetlist orgateTop.

(* A proof that the NAND-gate based implementation of the AND-gate is correct. *)
Lemma orgate_behaviour : forall (a : bool) (b : bool),
                         combinational (orgate a b) = a || b.
Proof.
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

(******************************************************************************)
(* Build an XOR-gate using only NAND gates.                                   *)
(******************************************************************************)

Definition xorgate {m t} `{Cava m t} a b :=
  nab <- nand_gate [a; b] ;;
  x <- nand_gate [a; nab] ;;
  y <- nand_gate [nab; b] ;;
  c <- nand_gate [x; y] ;;
  ret c.

Definition xorgateTop :=
  setModuleName "xorgate" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  c <- xorgate a b ;;
  outputBit "c" c.

Definition xorgateNetlist := makeNetlist xorgateTop.

(* A proof that the NAND-gate based implementation of the XOR-gate is correct. *)
Lemma xorgate_behaviour : forall (a : bool) (b : bool),
                          combinational (xorgate a b) = xorb a b.
Proof.
  intros.
  unfold combinational.
  unfold fst. 
  simpl.
  case a, b.
  all : reflexivity.
Qed.

(******************************************************************************)
(* Build a half-adder                                                         *)
(******************************************************************************)

Definition halfAdder {m t} `{Cava m t} a b :=
  partial_sum <- xorgate a b ;;
  carry <- andgate a b ;;
  ret (partial_sum, carry).

Definition halfAdderTop :=
  setModuleName "halfadder" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  '(ps, c) <- halfAdder a b ;;
  outputBit "partial_sum" ps ;;
  outputBit "carry" c.

Definition halfAdderNetlist := makeNetlist halfAdderTop.

(* A proof that the NAND-gate based implementation of the half-adder is correct. *)
Lemma halfAdder_behaviour : forall (a : bool) (b : bool),
                            combinational (halfAdder a b) = (xorb a b, a && b).

Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  case a, b.
  all : reflexivity.
Qed.

   
(******************************************************************************)
(* Build a full-adder                                                         *)
(******************************************************************************)

Definition fullAdder {m t} `{Cava m t} a b cin :=
  '(abl, abh) <- halfAdder a b ;;
  '(abcl, abch) <- halfAdder abl cin ;;
  cout <- orgate abh abch ;;
  ret (abcl, cout).

Definition fullAdderTop :=
  setModuleName "fulladder" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  cin <- inputBit "cin" ;;
  '(sum, cout) <- fullAdder a b cin ;;
  outputBit "sum" sum ;;
  outputBit "carry" cout.

Definition fullAdderNetlist := makeNetlist fullAdderTop.

(* A proof that the NAND-gate based implementation of the full-adder is correct. *)
Lemma fullAdder_behaviour : forall (a : bool) (b : bool) (cin : bool),
                            combinational (fullAdder a b cin)
                              = (xorb cin (xorb a b),
                                 (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold combinational.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.
