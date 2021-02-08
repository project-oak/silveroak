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

Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.BitVectorOps.
Require Import AcornAes.Pkg.
Require Import AesSpec.StateTypeConversions.
Require Import AesSpec.Tests.CipherTest.
Require Import AesSpec.Tests.Common.
Import Pkg.Notations.

Import VectorNotations.

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {monad: Monad cava}.

  (* Perform the bitwise XOR of two 4-element vectors of 8-bit values. *)
  Definition xor4xV
      (ab : signal (Vec (Vec Bit 8) 4) * signal (Vec (Vec Bit 8) 4))
      : cava (signal (Vec (Vec Bit 8) 4)) :=
    zipWith xorV (fst ab) (snd ab).

  (* Perform the bitwise XOR of two 4x4 matrices of 8-bit values. *)
  Definition xor4x4V (a b : signal state) : cava (signal state) :=
    zipWith xor4xV a b.

  Definition add_round_key (k : signal key) (st : signal state)
    : cava (signal state) := xor4x4V k st.
End WithCava.

(* add_round_key is internal to aes_cipher_core in OpenTitan and so does not have
* an "official" interface.
  https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_cipher_core.sv
*)
Definition add_round_key_Interface :=
  combinationalInterface "aes_add_round_key"
  [ mkPort "key_i" (Vec (Vec (Vec Bit 8) 4) 4);
    mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)]
  [].

Definition aes_add_round_key_Netlist
  := makeNetlist add_round_key_Interface (fun '(key_i, data_i) => add_round_key key_i data_i).

Definition test_state
  := [[219; 19; 83; 69];
      [242; 10; 34; 92];
      [1; 1; 1; 1];
      [45; 38; 49; 76]
  ].
Definition test_key
  := [[219; 19; 83; 69];
      [242; 10; 34; 92];
      [1; 1; 1; 1];
      [45; 38; 49; 76]
  ].

Local Open Scope list_scope.
(* Compute the expected outputs from the Coq/Cava semantics. *)
Definition add_round_key_expected_outputs : seqType (Vec (Vec (Vec Bit 8) 4) 4)
  := combinational (add_round_key [fromNatVec test_key] [fromNatVec test_state]).

Definition aes_add_round_key_tb :=
  testBench "aes_add_round_key_tb"
            add_round_key_Interface
            [(fromNatVec test_key, fromNatVec test_state)]
            add_round_key_expected_outputs.

(* Run test as a quick-feedback check *)
Import List.ListNotations.
Goal
  (let signal := combType in
   (* convert between flat-vector representation and state type *)
   let to_state : Vector.t bool 128 -> signal state :=
       fun st => map reshape (LittleEndian.to_cols_bits st) in
   let from_state : signal state -> Vector.t bool 128 :=
       fun st => LittleEndian.from_cols_bits (map flatten st) in
   (* run encrypt test with this version of add_round_key plugged in *)
   aes_test_encrypt Matrix
                    (fun step key =>
                       match step with
                       | AddRoundKey =>
                         fun st =>
                           let input := to_state st in
                           let k := to_state key in
                           let output := unIdent (add_round_key [k]%list [input]%list) in
                           from_state (List.hd (defaultCombValue _) output)
                       | _ => aes_impl step key
                       end) = Success).
Proof. vm_compute. reflexivity. Qed.
