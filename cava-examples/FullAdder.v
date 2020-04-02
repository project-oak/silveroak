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

From Coq Require Import Bool.Bool. 
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Monad.Cava.
Require Import Cava.BitArithmetic.

Local Open Scope list_scope.
Local Open Scope monad_scope.

(******************************************************************************)
(* Build a half-adder                                                         *)
(******************************************************************************)

Definition halfAdder {m t} `{Cava m t} a b :=
  partial_sum <- xor2 (a, b) ;;
  carry <- and2 (a, b) ;;
  ret (partial_sum, carry).

Definition halfAdderTop :=
  setModuleName "halfadder" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  '(ps, c) <- halfAdder a b ;;
  outputBit "partial_sum" ps ;;
  outputBit "carry" c.

Definition halfAdderNetlist := makeNetlist halfAdderTop.

(* A proof that the half-adder is correct. *)
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
  cout <- or2 (abh, abch) ;;
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

(* A proof that the the full-adder is correct. *)
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

(******************************************************************************)
(* Build a full-adder with explicit use of fast carry                                                        *)
(******************************************************************************)

Definition fullAdderFC {m bit} `{Cava m bit} (cin_ab : bit * (bit * bit))
  : m (bit * bit)%type :=
  let cin := fst cin_ab in
  let ab := snd cin_ab in
  let a := fst ab in
  let b := snd ab in
  part_sum <- xor2 (a, b) ;;
  sum <- xorcy (part_sum, cin) ;;
  cout <- muxcy part_sum a cin  ;;
  ret (sum, cout).

Definition fullAdderFCTop :=
  setModuleName "fulladderFC" ;;
  a <- inputBit "a" ;;
  b <- inputBit "b" ;;
  cin <- inputBit "cin" ;;
  '(sum, cout) <- fullAdderFC (cin, (a, b)) ;;
  outputBit "sum" sum ;;
  outputBit "carry" cout.

Definition fullAdderFCNetlist := makeNetlist fullAdderFCTop.

(* A proof that the the full-adder is correct. *)
Lemma fullAdderFC_behaviour : forall (a : bool) (b : bool) (cin : bool),
                              combinational (fullAdderFC (cin, (a, b)))
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



