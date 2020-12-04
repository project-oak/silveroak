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

From Coq Require Import Strings.Ascii Strings.String.
From Coq Require Import NArith.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Acorn.Identity.
Require Import Cava.Cava.
Require Import Cava.Tactics.
Require Import Cava.Monad.CavaMonad.
Require Import Cava.Lib.UnsignedAdders.

From Coq Require Import Bool.Bvector.

(******************************************************************************)
(* A byte unit delay.                                                         *)
(******************************************************************************)

Section WithCava.
  Context {signal} `{Cava signal} `{Monad cava}.

  Definition delayByte (i : signal (Vec Bit 8))
                       : cava (signal (Vec Bit 8)) :=
  delay i.

End WithCava.

Definition b0 := N2Bv_sized 8 0.
Definition b3 := N2Bv_sized 8 3.
Definition b7 := N2Bv_sized 8 7.
Definition b14 := N2Bv_sized 8 14.
Definition b18 := N2Bv_sized 8 18.
Definition b21 := N2Bv_sized 8 21.
Definition b24 := N2Bv_sized 8 24.
Definition b250 := N2Bv_sized 8 250.

Local Open Scope list_scope.

Example delay_ex1: sequential (delayByte [b14; b7; b250]) = [b0; b14; b7; b250].
Proof. reflexivity. Qed.

Lemma delayByteBehaviour: forall (i : list (Bvector 8)),
                          sequential (delayByte i) =  b0 :: i.
Proof.
  reflexivity.
Qed.

Definition delayByte_Interface
  := sequentialInterface "delayByte"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)]
     [].

Definition delayByte_Netlist := makeNetlist delayByte_Interface delayByte.

Definition delayByte_tb_inputs := [b14; b7; b250].

Definition delayByte_tb_expected_outputs
  := sequential (delayByte delayByte_tb_inputs).

Definition delayByte_tb
  := testBench "delayByte_tb" delayByte_Interface
      delayByte_tb_inputs delayByte_tb_expected_outputs.

(******************************************************************************)
(* A pipelined NAND gate.                                                     *)
(******************************************************************************)

Section WithCava.
  Context {signal} `{Cava signal} `{Monad cava}.

 (* A nand-gate with registers after the AND gate and the INV gate. *)
  Definition pipelinedNAND : signal Bit * signal Bit -> cava (signal Bit) :=
    nand2 >=> delay >=> inv >=> delay.

End WithCava.

Definition pipelinedNANDInterface
  := sequentialInterface "pipelinedNAND"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "a" Bit; mkPort "b" Bit]
     [mkPort "c"  Bit]
     [].

Definition pipelinedNANDNetlist :=
  makeNetlist pipelinedNANDInterface pipelinedNAND.


Definition pipelinedNAND_tb_inputs
  := ([true; false;  true; false; true;  false; true; false],
      [false; false; true; true;  false; false; true; true]
     ).

Definition pipelinedNAND_tb_expected_outputs
  := sequential (pipelinedNAND pipelinedNAND_tb_inputs).

Compute list (tupleSimInterface (circuitInputs pipelinedNANDInterface)).

(* TODO(satnam6502): Sequential interface for test-bench generation.
Definition pipelinedNAND_tb
  := testBench "pipelinedNAND_tb" pipelinedNANDInterface
     pipelinedNAND_tb_inputs pipelinedNAND_tb_expected_outputs.
*)

(******************************************************************************)
(* countBy                                                                    *)
(******************************************************************************) 

(*

The countBy circuit takes the current 8-bit input (in) and the current
state value represented by the register (delay) which is output in the
current cycle as the output of the circuit, and this value is also the
next state value for the delay. The adder is an 8-bit adder with no
bit-growth i.e. it computes (a + b) mod 256.

        _______
    ---| delay |------------
   |   |_______|            |
   |   ___                  |
    --| + ---------------------- out
 in --|___|     

*)

Section WithCava.
  Context {signal} {semantics:Cava signal} `{Monad cava}.

  Definition countFork (i : signal (Vec Bit 8) * signal (Vec Bit 8))
                       : cava (signal (Vec Bit 8) * signal (Vec Bit 8)) :=
    newCount <- addN (fst i) (snd i) ;;
    ret (newCount, newCount).

  Definition countBy : signal (Vec Bit 8) -> cava (signal (Vec Bit 8))
    := loop countFork.

End WithCava.

Example countBy_ex1: sequential (countBy [b14; b7; b3; b250]) = [b14; b21; b24; b18].
Proof. reflexivity. Qed.

Local Open Scope N_scope.

Fixpoint countBySpec' (state: Bvector 8) (i : list (Bvector 8))
                      : list (Bvector 8) :=
  match i with
  | [] => []
  | x::xs =>
    let newState := N2Bv_sized 8 (Bv2N x + Bv2N state) in
    newState :: countBySpec' newState xs
  end.

Definition countBySpec := countBySpec' (N2Bv_sized 8 0).

(* TODO: addN sequential seems to only return one result; shouldn't it be a map2? *)
Definition addNSpec {n} (a b : list (Bvector n)) : list (Bvector n) :=
  match a,b with
  | a :: _, b :: _ => [N2Bv_sized n ((Bv2N a + Bv2N b))]
  | _,_ => []
  end.

Local Ltac seqsimpl_step :=
  first [ progress cbn beta iota delta
                   [fst snd hd sequential loopSeq' loop SequentialCombSemantics]
        | progress cbv beta iota delta [loopSeq]; seqsimpl_step
        | progress autorewrite with seqsimpl
        | progress destruct_pair_let
        | progress simpl_ident ].
Local Ltac seqsimpl := repeat seqsimpl_step.

(* TODO: rename typeclass arguments *)
Lemma addNCorrect n (a b : list (Bvector n)) :
  sequential (addN (H:=SequentialCombSemantics) a b) = addNSpec a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : seqsimpl.

Lemma countForkStep:
  forall (i : Bvector 8) (s : Bvector 8),
    sequential (countFork (semantics:=SequentialCombSemantics) ([i], [s]))
    = (countBySpec' s [i], countBySpec' s [i]).
Proof.
  intros; cbv [countFork countBySpec'].
  seqsimpl; reflexivity.
Qed.
Hint Rewrite countForkStep using solve [eauto] : seqsimpl.

Lemma countForkCorrect:
  forall (i : list (Bvector 8)) (s : Bvector 8),
    sequential (loopSeq' (countFork (semantics:=SequentialCombSemantics)) i [s])
    = countBySpec' s i.
Proof.
  cbv [sequential]; induction i; intros; [ reflexivity | ].
  seqsimpl. cbn [countBySpec']; rewrite IHi; reflexivity.
Qed.
Hint Rewrite countForkCorrect using solve [eauto] : seqsimpl.

Lemma countByCorrect: forall (i : list (Bvector 8)),
                      sequential (countBy i) = countBySpec i.
Proof.
  intros; cbv [countBy countBySpec].
  seqsimpl; reflexivity.
Qed.
