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
From Coq Require Import Strings.Ascii Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaMonad.
Require Import Cava.Monad.XilinxAdder.

Section WithCava.
  Context {signal} `{Cava signal} `{Monad cava}.

  (****************************************************************************)
  (* Build a half-adder                                                       *)
  (****************************************************************************)

  Definition halfAdder '(a, b) :=
    partial_sum <- xor2 (a, b) ;;
    carry <- and2 (a, b) ;;
    ret (partial_sum, carry).

  (****************************************************************************)
  (* Build a full-adder                                                       *)
  (****************************************************************************)

  Definition fullAdder '(cin, (a, b)) :=
    '(abl, abh) <- halfAdder (a, b) ;;
    '(abcl, abch) <- halfAdder (abl, cin) ;;
    cout <- or2 (abh, abch) ;;
    ret (abcl, cout).

  Definition fullAdderTop '(cin, a, b) := fullAdder (cin, (a, b)).  

  (****************************************************************************)
  (* Now build an n-bit adder out of full-adders                              *)
  (****************************************************************************)

  Definition adder' := col fullAdder.

  Definition adder '(cin, (a, b)) :=
    adder' (cin, combine a b).

  Local Open Scope list_scope.

  Definition adderWithGrowth '(cin, (a, b)):=
    '(sum, carryOut) <- adder (cin, (a, b)) ;;
    ret (sum ++ [carryOut]).

End WithCava.

Definition halfAdderInterface
  := combinationalInterface "halfadder"
     [mkPort "a" Bit; mkPort "b" Bit]
     [mkPort "partial_sum" Bit; mkPort "carry" Bit]
     [].

Definition halfAdderNetlist := makeNetlist halfAdderInterface halfAdder.

(* A proof that the half-adder is correct. *)
Lemma halfAdder_behaviour : forall (a : bool) (b : bool),
                            combinational (halfAdder (a, b)) = (xorb a b, a && b).

Proof.
  auto.
Qed.

Definition fullAdderInterface
  := combinationalInterface "fullAdder"
     [mkPort "cin" Bit; mkPort "a" Bit; mkPort "b" Bit]
     [mkPort "sum" Bit; mkPort "carry" Bit]
     [].

Definition fullAdderNetlist := makeNetlist fullAdderInterface fullAdderTop.

Definition fullAdder_tb_inputs :=
  [(false, false, false);
   (false, true,  false);
   (false, false, true);
   (false, true,  true);
   (true,  false, false);
   (true,  true,  false);
   (true,  false, true);
   (true,  true,  true)
].

Definition fullAdder_tb_expected_outputs
   := map (fun i => combinational (fullAdderTop i)) fullAdder_tb_inputs.

Definition fullAdder_tb
  := testBench "fullAdder_tb" fullAdderInterface
     fullAdder_tb_inputs fullAdder_tb_expected_outputs.

(* A proof that the the full-adder is correct. *)
Lemma fullAdder_behaviour : forall (a : bool) (b : bool) (cin : bool),
                            combinational (fullAdderTop (cin, a, b))
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
                                combinational (fullAdderTop (cin, a, b)) =
                                combinational (xilinxFullAdder cin (a, b)).
Proof.
  intros.
  unfold combinational. simpl.
  case a, b, cin.
  all : reflexivity.
Qed.

