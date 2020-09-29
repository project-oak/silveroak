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

From ArrowExamples Require Import Combinators Aes.pkg Aes.mix_columns Aes.sbox Aes.sub_bytes Aes.shift_rows Aes.cipher_round.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

(* module aes_cipher_control ( *)
Definition aes_cipher_control
  (sbox_impl: SboxImpl)
  : <<
(*   input  logic                    in_valid_i, *)
(*   input  logic                    out_ready_i, *)
(*   input  aes_pkg::ciph_op_e       op_i, *)
(*   input  aes_pkg::key_len_e       key_len_i, *)
(*   input  logic                    crypt_i, *)
(*   input  logic                    dec_key_gen_i, *)
(*   input  logic                    key_clear_i, *)
(*   input  logic                    data_out_clear_i, *)
      Bit (* in_valid_i *)
    , Bit (* out_ready_i *)
    , ciph_op_e (* op_i *)
    , Bit (* crypt_i *)
    , Bit (* dec_key_gen_i *)
    , Bit (* key_clear_i *)
    , Bit (* data_out_clear_i *)
    , Unit
    >> ~>
    <<
(*   output logic                    in_ready_o, *)
(*   output logic                    out_valid_o, *)
(*   output logic                    crypt_o, *)
(*   output logic                    dec_key_gen_o, *)
(*   output logic                    key_clear_o, *)
(*   output logic                    data_out_clear_o, *)
      Bit (* in_ready_o *)
    , Bit (* out_valid_o *)
    , Bit (* crypt_o *)
    , Bit (* dec_key_gen_o *)
    , Bit (* key_clear_o *)
    , Bit (* data_out_clear_o *)

(*   output aes_pkg::state_sel_e     state_sel_o, *)
(*   output logic                    state_we_o, *)
(*   output aes_pkg::add_rk_sel_e    add_rk_sel_o, *)
    , state_sel_e (* state_sel_o *)
    , Bit (* state_we_o *)
    , add_rk_sel_e (* add_rk_sel_o, *)

(*   output aes_pkg::ciph_op_e       key_expand_op_o, *)
(*   output aes_pkg::key_full_sel_e  key_full_sel_o, *)
(*   output logic                    key_full_we_o, *)
(*   output aes_pkg::key_dec_sel_e   key_dec_sel_o, *)
(*   output logic                    key_dec_we_o, *)
(*   output logic                    key_expand_step_o, *)
(*   output logic                    key_expand_clear_o, *)
(*   output logic [3:0]              key_expand_round_o, *)
(*   output aes_pkg::key_words_sel_e key_words_sel_o, *)
(*   output aes_pkg::round_key_sel_e round_key_sel_o *)
    , ciph_op_e (* key_expand_op_o *)
    , key_full_sel_e (* key_full_sel_o *)
    , Bit (* key_full_we_o *)

    , key_dec_sel_e (* key_dec_sel_o, *)
    , Bit           (* key_dec_we_o, *)
    , Bit           (* key_expand_step_o, *)
    , Bit           (* key_expand_clear_o, *)
    , Vector Bit 4  (* key_expand_round_o, *)
    , key_words_sel_e (* key_words_sel_o, *)
    , round_key_sel_e (* round_key_sel_o *)
    >> :=
  <[\ in_valid_i out_ready_i op_i crypt_i dec_key_gen_i key_clear_i data_out_clear_i =>
  asd
  ]>.

