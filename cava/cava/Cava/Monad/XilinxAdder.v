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
Require Import Cava.Monad.Combinators.
Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.

(******************************************************************************)
(* Build a full-adder with explicit use of Xilinx FPGA fast carry logic       *)
(******************************************************************************)

Definition xilinxFullAdder {m bit} `{Cava m bit} '(cin, (a, b))
  : m (bit * bit)%type :=
  part_sum <- xor2 (a, b) ;;
  sum <- xorcy (part_sum, cin) ;;
  cout <- muxcy part_sum cin a  ;;
  ret (sum, cout).

(* A proof that the the full-adder is correct. *)
Lemma xilinxFullAdder_behaviour :
  forall (a : bool) (b : bool) (cin : bool),
         combinational (xilinxFullAdder (cin, (a, b)))
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
(* An unsigned adder built using the fast carry full-adder.                   *)
(******************************************************************************)

Definition xilinxAdderWithCarry {m bit} `{Cava m bit} '(cin, (a, b))
           : m (list bit * bit) 
  := col xilinxFullAdder (cin, combine a b).

(******************************************************************************)
(* An unsigned adder which does not have a carry-in and uses the carry-out    *)
(* for bit-growth at the output.                   *)
(******************************************************************************)

Local Open Scope list_scope.

Definition xilinxAdder {m bit} `{Cava m bit} a b : m (list bit) :=
  z <- zero ;;
  '(sum, carry) <- xilinxAdderWithCarry (z, (a, b)) ;;
  ret (sum ++ [carry]).

