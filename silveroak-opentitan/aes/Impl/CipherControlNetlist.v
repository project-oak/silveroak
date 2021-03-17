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
Require Import AesImpl.CipherControlCircuit.
Require Import AesImpl.SubBytesCircuit.
Require Import AesImpl.MixColumnsCircuit.
Require Import AesImpl.ShiftRowsCircuit.
Require Import AesImpl.AddRoundKeyCircuit.
Require Import AesImpl.Pkg.
Require AesImpl.CipherCircuit.
Import Pkg.Notations.

Require Import AesImpl.ShiftRowsNetlist.
Require Import AesImpl.MixColumnsNetlist.
Require Import AesImpl.SubBytesNetlist.

Definition aes_shift_rows' x y :=
  blackBoxNet aes_shift_rows_Interface (x, y).
Definition aes_mix_columns' x y :=
  blackBoxNet aes_mix_columns_Interface (x, y).
Definition aes_sbox_lut' x y :=
  blackBoxNet aes_sbox_lut_Interface (x, y).
Definition aes_sub_bytes' (is_decrypt : Signal Bit) (b : Signal state)
  : cava (Signal state) := Vec.map (Vec.map (aes_sbox_lut' is_decrypt)) b.

Definition inv_mix_columns_key := aes_mix_columns' (constant true).

(* Interface of existing aes_key_expand
* https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_key_expand.sv *)
Definition aes_key_expand_Interface :=
   sequentialInterface "aes_key_expand"
   "clk_i" PositiveEdge "rst_ni" NegativeEdge
   [ mkPort "op_i" Bit
   ; mkPort "step_i" Bit
   ; mkPort "clear_i" Bit
   ; mkPort "round_i" (Vec Bit 4)
   ; mkPort "key_len_i" (Vec Bit 3)
   ; mkPort "key_i" keypair
   ]
   [ mkPort "key_o" keypair ].

Definition aes_key_expand :
  Circuit _ _ :=
  Comb (blackBoxNet aes_key_expand_Interface).

Definition cipher_round := CipherCircuit.cipher_round
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
  [ mkPort "state_o" state ].

Definition cipher_round_Netlist
  := makeNetlist cipher_round_Interface
  (fun '(a, b, c, d, e, f ) => cipher_round a b c d e f).

Definition aes_cipher_core_Interface :=
  sequentialInterface "aes_cipher_core"
  "clk_i" PositiveEdge
  "rst_ni" NegativeEdge
  [ mkPort "in_valid_i" Bit
  ; mkPort "out_ready_i" Bit
  ; mkPort "crypt_i" Bit
  ; mkPort "dec_key_gen_i" Bit
  ; mkPort "key_clear_i" Bit
  ; mkPort "data_out_clear_i" Bit
  ; mkPort "op_i" Bit
  ; mkPort "key_len_i" (Vec Bit 3)

  ; mkPort "prng_data_i" state
  ; mkPort "state_init_i" state
  ; mkPort "key_init_i" keypair


  ]
  [ mkPort "in_ready_o" Bit
  ; mkPort "out_valid_o" Bit
  ; mkPort "crypt_o" Bit
  ; mkPort "dec_key_gen_o" Bit
  ; mkPort "key_clear_o" Bit
  ; mkPort "data_out_clear_o" Bit

  ; mkPort "state_o" state
  ].

Definition cipher_loop := CipherCircuit.cipher_loop
  (round_index:=round_index)
  aes_sub_bytes' aes_shift_rows' aes_mix_columns' aes_add_round_key
  inv_mix_columns_key.

Definition aes_cipher_loop_Interface :=
  sequentialInterface "aes_cipher_loop"
  "clk_i" PositiveEdge
  "rst_ni" NegativeEdge
  [ mkPort "op_i" Bit
  ; mkPort "num_rounds" round_index
  ; mkPort "round_0" round_index
  ; mkPort "curr_round" round_index
  ; mkPort "key1_i" key
  ; mkPort "state_i" state
  ; mkPort "key2_i" key
  ]
  [ mkPort "state_o" state
  ].

Definition aes_cipher_loop_Netlist :=
  makeCircuitNetlist aes_cipher_loop_Interface cipher_loop.

Definition aes_cipher_core := CipherControlCircuit.aes_cipher_core
  aes_key_expand cipher_loop.

Definition aes_cipher_core_Netlist
  := makeCircuitNetlist aes_cipher_core_Interface aes_cipher_core.
