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

Require Import Cava.Cava.
Import Circuit.Notations.

(******************************************************************************)
(* A byte unit delay.                                                         *)
(******************************************************************************)

Section WithCava.
  Context `{Cava}.

  Definition delayByte : Circuit (signal (Vec Bit 8)) (signal (Vec Bit 8)) :=
    Delay.

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

Example delay_ex1: simulate delayByte [b14; b7; b250] = [b0; b14; b7].
Proof. reflexivity. Qed.

Definition delayByte_Interface
  := sequentialInterface "delayByte"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)].

Definition delayByte_Netlist := makeCircuitNetlist delayByte_Interface delayByte.

Definition delayByte_tb_inputs := [b14; b7; b250].

Definition delayByte_tb_expected_outputs
  := simulate delayByte delayByte_tb_inputs.

Definition delayByte_tb
  := testBench "delayByte_tb" delayByte_Interface
      delayByte_tb_inputs delayByte_tb_expected_outputs.

(******************************************************************************)
(* A byte unit delay with enable.                                             *)
(******************************************************************************)

Section WithCava.
  Context `{Cava}.

  Definition delayEnableByte
    : Circuit (signal (Vec Bit 8) * signal Bit) (signal (Vec Bit 8)) :=
    DelayCE.

End WithCava.

Definition delayEnableByte_Interface
  := sequentialInterface "delayEnableByte"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" (Vec Bit 8); mkPort "en" Bit]
     [mkPort "o" (Vec Bit 8)].

Definition delayEnableByte_Netlist
  := makeCircuitNetlist delayEnableByte_Interface delayEnableByte.

(* The first output should be the default initial/reset value of the
   register i.e. followed by the input values that arrive with enable=1,
   with enable=0 input values ignored i.e. [0; 14; 14; 250]. The last
   input value influences the internal state but does not appear in the output
   stream.
*)
Definition delayEnableByte_tb_inputs :=
  [(b14, true); (b7, false); (b250, true); (b18, true)].

Example delayEnableByte_test:
  simulate delayEnableByte delayEnableByte_tb_inputs = [b0; b14; b14; b250].
Proof. reflexivity. Qed.

Definition delayEnableByte_tb_expected_outputs
  := simulate delayEnableByte delayEnableByte_tb_inputs.

Definition delayEnableByte_tb
  := testBench "delayEnableByte_tb" delayEnableByte_Interface
     delayEnableByte_tb_inputs delayEnableByte_tb_expected_outputs.

(******************************************************************************)
(* A pipelined NAND gate.                                                     *)
(******************************************************************************)

Section WithCava.
  Context `{semantics: Cava}.

 (* A nand-gate with registers after the AND gate and the INV gate. *)
  Definition pipelinedNAND : Circuit (signal Bit * signal Bit) (signal Bit) :=
    Comb nand2 >==> Delay >==> Comb inv >==> Delay.

End WithCava.

Definition pipelinedNANDInterface
  := sequentialInterface "pipelinedNAND"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "a" Bit; mkPort "b" Bit]
     [mkPort "c"  Bit].

Definition pipelinedNANDNetlist :=
  makeCircuitNetlist pipelinedNANDInterface pipelinedNAND.

Definition pipelinedNAND_tb_inputs
  := [(true, false);
     (false, false);
     (true,  true);
     (false, true);
     (true,  false);
     (false, false);
     (true,  true);
     (false, true)].

(*
     _______    ______    _____    ______
a --|       |  |      |  |     |  |      |
    | nand2 |--| reg1 |--| inv |--| reg2 |-- out
b --|_______|  |______|  |_____|  |______|


reg1[0] = reg2[0] = 0
reg1[t] = nand a[t] b[t]
reg2[t] = inv reg1[t-1]
out = reg2[t-1]

Test:

t    0  1  2  3  4  5  6  7
---------------------------
a    1  0  1  0  1  0  1  0
b    0  0  1  1  0  0  1  1
reg1 1  1  0  1  1  1  0  1
reg2 1  0  0  1  0  0  0  1
out  0  1  0  0  1  0  0  0
 *)

Example pipelinedNAND_test:
  simulate pipelinedNAND pipelinedNAND_tb_inputs
  = [false; true; false; false; true; false; false; false].
Proof. reflexivity. Qed.

Definition pipelinedNAND_tb_expected_outputs
  := simulate pipelinedNAND pipelinedNAND_tb_inputs.

Definition pipelinedNAND_tb
  := testBench "pipelinedNAND_tb" pipelinedNANDInterface
     pipelinedNAND_tb_inputs pipelinedNAND_tb_expected_outputs.
