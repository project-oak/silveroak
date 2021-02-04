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

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.UnsignedAdders.

From Coq Require Import Bool.Bvector.

(******************************************************************************)
(* A byte unit delay.                                                         *)
(******************************************************************************)

Section WithCava.
  Context `{CavaSeq}.

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
(* A byte unit delay with enable.                                             *)
(******************************************************************************)

Section WithCava.
  Context `{CavaSeq}.

  Definition delayEnableByte (en_i : signal Bit * signal (Vec Bit 8))
                             : cava (signal (Vec Bit 8)) :=
  let (en, i) := en_i in                           
  delayEnable en i.

End WithCava.

Definition delayEnableByte_Interface
  := sequentialInterface "delayEnableByte"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "en" Bit; mkPort "i" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)]
     [].

Definition delayEnableByte_Netlist
  := makeNetlist delayEnableByte_Interface delayEnableByte.

(* Ideally we want to provide this representation for the sequential test
   inputs i.e. delayEnableByte_transposed_tb_inputs and then automatically
   compute delayEnableByte_tb_inputs but for the moment we explicitly provide
   both versions. Likewise for the output types.
   TODO(satnam6502): Write appropriate transpose functions that maps:
     list (tupleInterface combType [t1; t2; ... tN]])
   to:
     tupleInterface seqType [t1; t2; ... tN]
*)
Definition delayEnableByte_transposed_tb_inputs : list (tupleInterface combType [Bit; Vec Bit 8]) :=
  [(true,  b14);
   (false, b7);
   (true,  b250);
   (true,  b18)
  ].

(* The first output should be the default initial/reset value of the
   register i.e. followed by the input values that arrive with enable=1,
   with enable=0 input values ignored i.e. [0; 14; 14; 250]. The last
   input value influences the internal state but does not appear in the output
   stream.
*)
Definition delayEnableByte_tb_inputs : tupleInterface seqType [Bit; Vec Bit 8]
  := ([true; false; true; true],
      [b14;  b7;    b250; b18]).

Example delayEnableByte_test:
  sequential (delayEnableByte delayEnableByte_tb_inputs) = [b0; b14; b14; b250].
Proof. reflexivity. Qed.

Definition delayEnableByte_tb_expected_outputs
  := sequential (delayEnableByte delayEnableByte_tb_inputs).

Definition delayEnableByte_tb
  := testBench "delayEnableByte_tb" delayEnableByte_Interface
     delayEnableByte_transposed_tb_inputs [b0; b14; b14; b250].

(******************************************************************************)
(* A pipelined NAND gate.                                                     *)
(******************************************************************************)

Section WithCava.
  Context `{semantics: CavaSeq}.

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

(* TODO(satnam6502): Sequential interface for test-bench generation.
Compute list (tupleSimInterface (circuitInputs pipelinedNANDInterface)).
Definition pipelinedNAND_tb
  := testBench "pipelinedNAND_tb" pipelinedNANDInterface
     pipelinedNAND_tb_inputs pipelinedNAND_tb_expected_outputs.
*)
