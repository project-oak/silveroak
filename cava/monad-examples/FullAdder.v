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
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
From Coq Require Import Lists.List.
Require Import Omega.
Import ListNotations.

Require Import Nat Arith Lia.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Monad.Cava.
Require Import Cava.Netlist.
Require Import Cava.Monad.Combinators.
Require Import Cava.BitArithmetic.
Require Import Cava.Monad.XilinxAdder.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(******************************************************************************)
(* Build a half-adder                                                         *)
(******************************************************************************)

Definition halfAdder {m t} `{Cava m t} '(a, b) :=
  partial_sum <- xor2 (a, b) ;;
  carry <- and2 (a, b) ;;
  ret (partial_sum, carry).

Definition halfAdderInterface
  := mkCircuitInterface "halfadder"
     (Tuple2 (One ("a", Bit)) (One ("b", Bit)))
     (Tuple2 (One ("partial_sum", Bit)) (One ("carry", Bit)))
     [].

Definition halfAdderNetlist := makeNetlist halfAdderInterface halfAdder.

(* A proof that the half-adder is correct. *)
Lemma halfAdder_behaviour : forall (a : bool) (b : bool),
                            combinational (halfAdder (a, b)) = (xorb a b, a && b).

Proof.
  auto.
Qed.

   
(******************************************************************************)
(* Build a full-adder                                                         *)
(******************************************************************************)

Definition fullAdder {m t} `{Cava m t} '(cin, (a, b)) :=
  '(abl, abh) <- halfAdder (a, b) ;;
  '(abcl, abch) <- halfAdder (abl, cin) ;;
  cout <- or2 (abh, abch) ;;
  ret (abcl, cout).

Definition fullAdderInterface
  := mkCircuitInterface "fullAdder"
     (Tuple2 (One ("cin", Bit)) (Tuple2 (One ("a", Bit)) (One ("b", Bit))))
     (Tuple2 (One ("sum", Bit)) (One ("carry", Bit)))
     [].

Definition fullAdderNetlist := makeNetlist fullAdderInterface fullAdder.

Definition fullAdder_tb_inputs :=
  [(false, (false, false));
   (false, (true, false));
   (false, (false, true));
   (false, (true, true));
   (true, (false, false));
   (true, (true, false));
   (true, (false, true));
   (true, (true, true))
].

Definition fullAdder_tb_expected_outputs
   := map (fun i => combinational (fullAdder i)) fullAdder_tb_inputs.

Definition fullAdder_tb
  := testBench "fullAdder_tb" fullAdderInterface
     fullAdder_tb_inputs fullAdder_tb_expected_outputs.

(* A proof that the the full-adder is correct. *)
Lemma fullAdder_behaviour : forall (a : bool) (b : bool) (cin : bool),
                            combinational (fullAdder (cin, (a, b)))
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

(* Prove the generic full adder is equivalent to Xilinx fast adder. *)
Lemma generic_vs_xilinx_adder : forall (a : bool) (b : bool) (cin : bool),
                                combinational (fullAdder (cin, (a, b))) =
                                combinational (xilinxFullAdder (cin, (a, b))).
Proof.
  intros. 
  unfold combinational. simpl.
  case a, b, cin.
  all : reflexivity.
Qed.

(******************************************************************************)
(* Now build an n-bit adder out of full-adders                                *)
(******************************************************************************)

Definition adder' {m bit} `{Cava m bit} := col fullAdder.

Definition adder {m bit} `{Cava m bit} '(cin, (a, b)) :=
  adder' (cin, combine a b).

Local Open Scope list_scope.

Definition adderWithGrowth {m bit} `{Cava m bit} '(cin, (a, b)):=
  '(sum, carryOut) <- adder (cin, (a, b)) ;;
  ret (sum ++ [carryOut]).

  

