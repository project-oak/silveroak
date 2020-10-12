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
From Cava Require Import Arrow.ArrowExport BitArithmetic.

From Aes Require Import pkg mix_columns sbox sub_bytes shift_rows cipher_round key_expand.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

Definition aes_cipher_core
  (sbox_impl: SboxImpl)
  : <<
  (* input  logic                 in_valid_i, *)
  Bit,
  (* input  logic                 out_ready_i, *)
  Bit,
  (* input  logic                 cfg_valid_i, // Used for gating assertions only. *)
  Bit,
  (* input  ciph_op_e             op_i, *)
  ciph_op_e,
  (* input  key_len_e             key_len_i, *)
  (* key_len_e, *)
  (* input  logic                 crypt_i, *)
  Bit,
  (* input  logic                 dec_key_gen_i, *)
  Bit,
  (* input  logic                 key_clear_i, *)
  Bit,
  (* input  logic                 data_out_clear_i, // Re-use the cipher core muxes. *)
  Bit,
  (* input  logic [3:0][3:0][7:0] state_init_i [NumShares], *)
  Vector (Vector (Vector Bit 8) 4) 4,
  (* input  logic     [7:0][31:0] key_init_i [NumShares], *)
  Vector (Vector (Vector Bit 8) 4) 8,
  Unit >>
  ~> <<
  (* output logic                 in_ready_o, *)
  Bit,
  (* output logic                 out_valid_o, *)
  Bit,
  (* output logic                 crypt_o, *)
  Bit,
  (* output logic                 dec_key_gen_o, *)
  Bit,
  (* output logic                 key_clear_o, *)
  Bit,
  (* output logic                 data_out_clear_o, *)
  Bit
  >>
  :=
  <[\in_valid_i
    out_ready_i
    cfg_valid_i
    op_i
    (* key_len_i *)
    crypt_i
    dec_key_gen_i
    key_clear_i
    data_out_clear_i
    state_init_i
    key_init_i =>

    letrec state =
      let
        '( last_keys
        , last_op_i
        , last_data
        , last_round
        , last_in_ready
        ) : <<
            Vector (Vector (Vector Bit 8) 4) 8
          , ciph_op_e
          , Vector (Vector (Vector Bit 8) 4) 4
          , Vector Bit 4
          , Bit
        >> = state in

      let start_new_round = not last_in_ready && in_valid_i in

      let
        '(cipher_mode
        , data_input
        , round
        , key) =
          if start_new_round
          then (op_i, !aes_transpose state_init_i, #0, key_init_i)
          else (last_op_i, last_data, last_round +% #1, last_keys) in

      let is_first_round = round == #0 in
      let is_final_round = round == #13 in

      let step_i = true' in
      let clear_i = round == #0 in

      let key_words = !aes_transpose
        (if op_i == !CIPH_FWD
        then key[:7:4]
        else key[:3:0])
        in
      let round_key =
        if op_i == !CIPH_FWD
        then key_words
        else !aes_mix_columns !CIPH_INV key_words in

      let data_o =
          !(cipher_round_combined sbox_impl) cipher_mode data_input round_key is_first_round is_final_round in

      let keys = !(aes_key_expand sbox_impl) cipher_mode step_i clear_i round last_keys in

      ( keys
      , op_i
      , data_input
      , round
      , last_in_ready
      )

      in

    let out_valid_o = false' in
    let crypt_o = false' in
    let dec_key_gen_o = false' in
    let key_clear_o = false' in
    let data_out_clear_o = false' in
    (
      (* output logic                 in_ready_o, *)
    false' ,
      (* output logic                 out_valid_o, *)
    out_valid_o ,
      (* output logic                 crypt_o, *)
    crypt_o ,
      (* output logic                 dec_key_gen_o, *)
    dec_key_gen_o ,
      (* output logic                 key_clear_o, *)
    key_clear_o ,
      (* output logic                 data_out_clear_o, *)
    data_out_clear_o
    )

    ]>.



