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

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.
Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import AcornAes.CipherControlCircuit.
Require Import AcornAes.SubBytesCircuit.
Require Import AcornAes.MixColumnsCircuit.
Require Import AcornAes.ShiftRowsCircuit.
Require Import AcornAes.AddRoundKeyCircuit.
Require Import AcornAes.Pkg.
Require AcornAes.CipherNewLoop.
Import Pkg.Notations.

Require Import AcornAes.ShiftRowsNetlist.
Require Import AcornAes.MixColumnsNetlist.

Definition cipher_round := CipherNewLoop.cipher_round
  (round_index:=round_index)
  aes_sub_bytes' aes_shift_rows' aes_mix_columns' aes_add_round_key
  inv_mix_columns_key.

Definition cipher_round_Interface :=
  combinationalInterface "cipher_round"
  [ mkPort "is_decrypt" Bit
  ; mkPort "key" key
  ; mkPort "add_round_key_in_sel" (Vec Bit 2)
  ; mkPort "round_key_sel" Bit
  ; mkPort "round_i" (Vec Bit 4)
  ; mkPort "data" state ]
  [ mkPort "state_o" state ]
  [].

Definition cipher_round_Netlist
  := makeNetlist cipher_round_Interface
  (fun '(a, b, c, d, e, f ) => cipher_round a b c d e f).

Definition aes_cipher_core_simplified_Interface :=
  combinationalInterface "aes_cipher_core_simplified"
  [ mkPort "op_i" Bit
  ; mkPort "in_valid_i" Bit
  ; mkPort "out_ready_i" Bit
  ; mkPort "key_init_i" key
  ; mkPort "state_init_i" state ]
  [ mkPort "in_ready_o" Bit
  ; mkPort "out_valid_o" Bit
  ; mkPort "state_o" state ]
  [].

Definition aes_cipher_core_simplified_Netlist :=
  let aes := aes_cipher_core_simplified key_expand in
  makeCircuitNetlist aes_cipher_core_simplified_Interface aes.


