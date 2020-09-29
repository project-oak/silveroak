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

From Coq Require Import Arith Eqdep_dec Vector Lia NArith Omega String Ndigits.
From Arrow Require Import Category Arrow.
From Cava Require Import Arrow.ArrowExport BitArithmetic.

From ArrowExamples Require Import Combinators Aes.pkg Aes.mix_columns Aes.sbox Aes.sub_bytes Aes.shift_rows Aes.cipher_round .

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

(* module aes_cipher_core import aes_pkg::*; *)
(* #( *)
(*   parameter bit         AES192Enable = 1, *)
(*   parameter bit         Masking      = 0, *)
(*   parameter sbox_impl_e SBoxImpl     = SBoxImplLut, *)

(*   localparam int        NumShares    = Masking ? 2 : 1 // derived parameter *)
(* ) ( *)
(*   input  logic                 clk_i, *)
(*   input  logic                 rst_ni, *)

(*   // Input handshake signals *)
(*   input  logic                 in_valid_i, *)
(*   output logic                 in_ready_o, *)

(*   // Output handshake signals *)
(*   output logic                 out_valid_o, *)
(*   input  logic                 out_ready_i, *)

(*   // Control and sync signals *)
(*   input  logic                 cfg_valid_i, // Used for gating assertions only. *)
(*   input  ciph_op_e             op_i, *)
(*   input  key_len_e             key_len_i, *)
(*   input  logic                 crypt_i, *)
(*   output logic                 crypt_o, *)
(*   input  logic                 dec_key_gen_i, *)
(*   output logic                 dec_key_gen_o, *)
(*   input  logic                 key_clear_i, *)
(*   output logic                 key_clear_o, *)
(*   input  logic                 data_out_clear_i, // Re-use the cipher core muxes. *)
(*   output logic                 data_out_clear_o, *)

(*   // Pseudo-random data *)
(*   input  logic          [63:0] prng_data_i, *)

(*   // I/O data & initial key *)
(*   input  logic [3:0][3:0][7:0] state_init_i [NumShares], *)
(*   input  logic     [7:0][31:0] key_init_i [NumShares], *)
(*   output logic [3:0][3:0][7:0] state_o [NumShares] *)
(* ); *)

Definition aes_cipher_core
  (sbox_impl: SboxImpl)
  : <<
      Bit (* in_valid_i *)
    , Bit (* out_ready_i *)
    , Bit (* op_i *)
    , Bit (* crypt_i *)
    , Bit (* dec_key_gen_i *)
    , Bit (* key_clear_i *)
    , Bit (* data_out_clear_i *)
    , Vector Bit 64 (* prng_data_i *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* state_init_i *)
    , Vector (Vector Bit 32) 8 (* key_init_i *)
    , Unit
    >> ~>
    <<
      Bit (* in_ready_o *)
    , Bit (* out_valid_o *)
    , Bit (* crypt_o *)
    , Bit (* dec_key_gen_o *)
    , Bit (* key_clear_o *)
    , Bit (* data_out_clear_o *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* state_o *)
    >> :=
  <[\in_valid_i out_read_i op_i crypt_i dec_key_gen_i key_clear_i data_out_clear_i prng_data_i state_init_i key_init_i =>
  (* // Signals *)
  (* logic [3:0][3:0][7:0] state_d [NumShares]; *)
  (* logic [3:0][3:0][7:0] state_q [NumShares]; *)
  (* logic                 state_we; *)
  (* state_sel_e           state_sel; *)

  (* logic [3:0][3:0][7:0] sub_bytes_out; *)
  (* logic [3:0][3:0][7:0] sb_in_mask; *)
  (* logic [3:0][3:0][7:0] sb_out_mask; *)
  (* logic [3:0][3:0][7:0] shift_rows_in [NumShares]; *)
  (* logic [3:0][3:0][7:0] shift_rows_out [NumShares]; *)
  (* logic [3:0][3:0][7:0] mix_columns_out [NumShares]; *)
  (* logic [3:0][3:0][7:0] add_round_key_in [NumShares]; *)
  (* logic [3:0][3:0][7:0] add_round_key_out [NumShares]; *)
  (* add_rk_sel_e          add_round_key_in_sel; *)

  (* logic     [7:0][31:0] key_full_d [NumShares]; *)
  (* logic     [7:0][31:0] key_full_q [NumShares]; *)
  (* logic                 key_full_we; *)
  (* key_full_sel_e        key_full_sel; *)
  (* logic     [7:0][31:0] key_dec_d [NumShares]; *)
  (* logic     [7:0][31:0] key_dec_q [NumShares]; *)
  (* logic                 key_dec_we; *)
  (* key_dec_sel_e         key_dec_sel; *)
  (* logic     [7:0][31:0] key_expand_out [NumShares]; *)
  (* ciph_op_e             key_expand_op; *)
  (* logic                 key_expand_step; *)
  (* logic                 key_expand_clear; *)
  (* logic           [3:0] key_expand_round; *)
  (* key_words_sel_e       key_words_sel; *)
  (* logic     [3:0][31:0] key_words [NumShares]; *)
  (* logic [3:0][3:0][7:0] key_bytes [NumShares]; *)
  (* logic [3:0][3:0][7:0] key_mix_columns_out [NumShares]; *)
  (* logic [3:0][3:0][7:0] round_key [NumShares]; *)
  (* round_key_sel_e       round_key_sel; *)

  (* logic         [255:0] prng_data_256; *)
  in_valid_i
  ]>.
