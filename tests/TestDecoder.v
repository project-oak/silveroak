(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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
Require Import Cava.Lib.Decoder.

Definition packBit {n} := @packV combType Combinational.CombinationalSemantics Bit n.

Example ex1 : decoder (N2Bv_sized 1 0) = packBit [true; false].
Proof. trivial. Qed.
Example ex2 : decoder (N2Bv_sized 1 1) = packBit [false; true].
Proof. trivial. Qed.

Example ex3 : decoder (N2Bv_sized 2 0) = packBit [true; false; false; false].
Proof. trivial. Qed.
Example ex4 : decoder (N2Bv_sized 2 1) = packBit [false; true; false; false].
Proof. trivial. Qed.
Example ex5 : decoder (N2Bv_sized 2 2) = packBit [false; false; true; false].
Proof. trivial. Qed.
Example ex6 : decoder (N2Bv_sized 2 3) = packBit [false; false; false; true].
Proof. trivial. Qed.

Definition encoderBit {n} := @encoder combType Combinational.CombinationalSemantics n.

Example ex7  : encoderBit (decoder (N2Bv_sized 2 0)) = (N2Bv_sized 2 0).
Proof. trivial. Qed.
Example ex8  : encoderBit (decoder (N2Bv_sized 2 1)) = (N2Bv_sized 2 1).
Proof. trivial. Qed.
Example ex9  : encoderBit (decoder (N2Bv_sized 2 2)) = (N2Bv_sized 2 2).
Proof. trivial. Qed.
Example ex10 : encoderBit (decoder (N2Bv_sized 2 3)) = (N2Bv_sized 2 3).
Proof. trivial. Qed.

Definition N2hotv {n} k : Bvector n := Vector.reverse (unfold_ix tt (fun ix tt => (Nat.eqb k ix, tt))).

Example ex11  : encoderBit (N2hotv 2) = (N2Bv_sized 2 2).
Proof. trivial. Qed.

Definition decoderInterface (n: nat)
  := combinationalInterface "decoder"
     [mkPort "v" (Vec Bit n)]
     [mkPort "o" (Vec Bit (2^n))].

Definition decoder2Netlist := makeNetlist (decoderInterface 2) decoder.

Definition decoder2_tb_inputs : list (Bvector 2) :=
  [N2Bv_sized 2 0; N2Bv_sized 2 1; N2Bv_sized 2 2; N2Bv_sized 2 3].

Definition decoder2_expected_outputs : list (Bvector 4)
  := simulate (Comb decoder) decoder2_tb_inputs.

Definition decoder2_tb
  := testBench "decoder_tb"
     (decoderInterface 2) decoder2_tb_inputs
     decoder2_expected_outputs.

Definition encoderInterface (n: nat)
  := combinationalInterface "encoder"
     [mkPort "v" (Vec Bit (2^n))]
     [mkPort "o" (Vec Bit n)].

Definition encoder2Netlist := makeNetlist (encoderInterface 2) encoder.

Definition encoder2_tb_inputs : list (Bvector 4) :=
  [N2hotv 0; N2hotv 1; N2hotv 2; N2hotv 3].

Definition encoder2_expected_outputs : list (Bvector 2)
  := simulate (Comb (@encoder _ _ 2)) encoder2_tb_inputs.

Definition encoder2_tb
  := testBench "encoder_tb"
     (encoderInterface 2) encoder2_tb_inputs
     encoder2_expected_outputs.

Definition encoderdecoderInterface (n: nat)
  := combinationalInterface "encoderdecoder"
     [mkPort "v" (Vec Bit n)]
     [mkPort "o" (Vec Bit n)].

Definition encoderdecoderNetlist
  := makeNetlist (encoderdecoderInterface 4) (decoder >=> encoder).

Definition encoderdecoder_tb_inputs : list (Bvector 4) :=
  [N2Bv_sized 4 0;
   N2Bv_sized 4 1;
   N2Bv_sized 4 2;
   N2Bv_sized 4 3;
   N2Bv_sized 4 4;
   N2Bv_sized 4 5;
   N2Bv_sized 4 6;
   N2Bv_sized 4 7;
   N2Bv_sized 4 8;
   N2Bv_sized 4 9;
   N2Bv_sized 4 10;
   N2Bv_sized 4 11;
   N2Bv_sized 4 12;
   N2Bv_sized 4 13;
   N2Bv_sized 4 14;
   N2Bv_sized 4 15;
   N2Bv_sized 4 16].

Definition encoderdecoder_tb
  := testBench "encoderdecoder_tb"
     (encoderdecoderInterface 4) encoderdecoder_tb_inputs encoderdecoder_tb_inputs.
