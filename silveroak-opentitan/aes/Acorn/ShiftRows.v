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

Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Ndigits.
Import ListNotations.
Require Import Cava.Cava.

Require Import Coq.Vectors.Vector.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.


Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.BitVectorOps.
Require Import AcornAes.Pkg.
Require Import AesSpec.Tests.CipherTest.
Require Import AesSpec.Tests.Common.
Require Import AesSpec.StateTypeConversions.
Import Pkg.Notations.

Import VectorNotations.

Local Notation byte := (Vec Bit 8) (only parsing).
Local Notation "v [@ n ]" := (indexConst v n) (at level 1, format "v [@ n ]").

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {monad: Monad cava}.

  Definition aes_circ_byte_shift (shift: nat) (input: signal (Vec byte 4)):
    cava (signal (Vec byte 4)) :=
    let indices := [4 - shift; 5 - shift; 6 - shift; 7 - shift] in
    let indices := map (fun x => Nat.modulo x 4) indices in
    ret (unpeel (map (indexConst input) indices))
    .

  Definition aes_shift_rows
    (op_i: signal Bit)
    (data_i: signal (Vec (Vec byte 4) 4))
    : cava (signal (Vec (Vec byte 4) 4)) :=
  (* // Row 0 is left untouched *)
  (* assign data_o[0] = data_i[0]; *)
  let data_o_0 := data_i[@0] in
  (* // Row 2 does not depend on op_i *)
  (* assign data_o[2] = aes_circ_byte_shift(data_i[2], 2'h2); *)
  data_o_2 <- aes_circ_byte_shift 2 data_i[@2] ;;

  (* // Row 1 *)
  (* assign data_o[1] = (op_i == CIPH_FWD) ? aes_circ_byte_shift(data_i[1], 2'h3) *)
  (*                                       : aes_circ_byte_shift(data_i[1], 2'h1); *)
  data_o_1_0 <- aes_circ_byte_shift 3 data_i[@1] ;;
  data_o_1_1 <- aes_circ_byte_shift 1 data_i[@1] ;;
  data_o_1 <- muxPair op_i (data_o_1_0, data_o_1_1) ;;

  (* // Row 3 *)
  (* assign data_o[3] = (op_i == CIPH_FWD) ? aes_circ_byte_shift(data_i[3], 2'h1) *)
  (*                                       : aes_circ_byte_shift(data_i[3], 2'h3); *)
  data_o_3_0 <- aes_circ_byte_shift 1 data_i[@3] ;;
  data_o_3_1 <- aes_circ_byte_shift 3 data_i[@3] ;;
  data_o_3 <- muxPair op_i (data_o_3_0, data_o_3_1) ;;

  ret (unpeel [data_o_0; data_o_1; data_o_2; data_o_3]).

End WithCava.

(* Interface designed to match interface of corresponding SystemVerilog component:
     https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_shift_rows.sv
*)
Definition aes_shift_rows_Interface :=
  combinationalInterface "aes_shift_rows"
  [mkPort "op_i" Bit; mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)]
  [].

Definition aes_shift_rows_Netlist
  := makeNetlist aes_shift_rows_Interface (fun '(op_i, data_i) => aes_shift_rows op_i data_i).

(* Run test as a quick-feedback check *)
Require Import Cava.BitArithmetic.
Require Import AesSpec.StateTypeConversions.

Import List.ListNotations.
Goal
  (let signal := combType in
  let to_state : Vector.t bool 128 -> signal state :=
      fun st => Vector.map (Vector.map (fun r => byte_to_bitvec r)) (BigEndian.to_rows st) in
  let from_state : signal state -> Vector.t bool 128 :=
      fun st => BigEndian.from_rows (Vector.map (Vector.map (fun r => bitvec_to_byte r)) st) in

   (* run encrypt test with this version of aes_mix_columns plugged in *)
   aes_test_encrypt Matrix
                    (fun step key =>
                       match step with
                       | ShiftRows =>
                         fun st =>
                           let input := to_state st in
                           let output := unIdent (aes_shift_rows [false]%list [input]%list) in
                           from_state (List.hd (defaultCombValue _) output)
                       | _ => aes_impl step key
                       end) = Success).
Proof. vm_compute. reflexivity. Qed.

Definition shiftRowsTestVec : Vector.t (Vector.t nat 4) 4
  := [[219; 19; 83; 69];
      [242; 10; 34; 92];
      [1; 1; 1; 1];
      [45; 38; 49; 76]
  ].

Local Open Scope list_scope.

(* Compute the expected outputs from the Coq/Cava semantics. *)
Definition shift_rows_expected_outputs := combinational (aes_shift_rows [false] [fromNatVec shiftRowsTestVec]).

Definition aes_shift_rows_tb :=
  testBench "aes_shift_rows_tb"
            aes_shift_rows_Interface
            [(false, fromNatVec shiftRowsTestVec)]
            shift_rows_expected_outputs.
