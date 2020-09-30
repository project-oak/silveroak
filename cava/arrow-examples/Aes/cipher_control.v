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

(* typedef enum logic [2:0] { *)
(*   IDLE, INIT, ROUND, FINISH, CLEAR_S, CLEAR_KD *)
(* } aes_cipher_ctrl_e; *)
Definition aes_cipher_ctrl_e := Vector Bit 3.
Definition IDLE: Unit ~> aes_cipher_ctrl_e := <[ #0 ]>.
Definition INIT: Unit ~> aes_cipher_ctrl_e := <[ #1 ]>.
Definition ROUND: Unit ~> aes_cipher_ctrl_e := <[ #2 ]>.
Definition FINISH: Unit ~> aes_cipher_ctrl_e := <[ #3 ]>.
Definition CLEAR_S: Unit ~> aes_cipher_ctrl_e := <[ #4 ]>.
Definition CLEAR_KD: Unit ~> aes_cipher_ctrl_e := <[ #5 ]>.

Definition aes_cipher_control_state :=
  (* aes_cipher_ctrl_cs *)
  << aes_cipher_ctrl_e
  (* logic [3:0] round_d, round_q; *)
  ,  Vector Bit 4
  (* logic [3:0] num_rounds_d, num_rounds_q; *)
  , Vector Bit 4
  (* logic       crypt_d, crypt_q; *)
  , Bit
  (* logic       dec_key_gen_d, dec_key_gen_q; *)
  , Bit
  (* logic       key_clear_d, key_clear_q; *)
  , Bit
  (* logic       data_out_clear_d, data_out_clear_q; *)
  , Bit
  >>.

Definition aes_cipher_control_input :=
  (* input  logic                    in_valid_i, *)
  << Bit
  (* input  logic                    out_ready_i, *)
  , Bit
  (* input  aes_pkg::ciph_op_e       op_i, *)
  , ciph_op_e
  (* input  logic                    crypt_i, *)
  , Bit
  (* input  logic                    dec_key_gen_i, *)
  , Bit
  (* input  logic                    key_clear_i, *)
  , Bit
  (* input  logic                    data_out_clear_i, *)
  , Bit
  >>.

Definition aes_cipher_control_transition
  : <<aes_cipher_control_state, aes_cipher_control_input, Unit>> ~> aes_cipher_control_state
  :=
  <[ \ state input =>
    let '( aes_cipher_ctrl_cs
         , round_q
         , num_rounds_q
         , crypt_q
         , dec_key_gen_q
         , key_clear_q
         , data_out_clear_q
         ) = state in

    let '( in_valid_i
         , out_ready_i
         , op_i
         , crypt_i
         , dec_key_gen_i
         , key_clear_i
         , data_out_clear_i
         ) = input in

    if aes_cipher_ctrl_cs == !IDLE then
      (* IDLE: begin *)
      (*   dec_key_gen_d = 1'b0; *)
      let dec_key_gen_d = #0 in
      (*   // Signal that we are ready, wait for handshake. *)
      (*   in_ready_o = 1'b1; *)

      (*   if (in_valid_i) begin *)
      (*     if (key_clear_i || data_out_clear_i) begin *)
      if in_valid_i then
        if (key_clear_i || data_out_clear_i) then
      (*       // Clear internal key registers. The cipher core muxes are used to clear the data *)
      (*       // output registers. *)
      (*       key_clear_d      = key_clear_i; *)
      (*       data_out_clear_d = data_out_clear_i; *)

      (*       // To clear the data output registers, we must first clear the state. *)
      (*       aes_cipher_ctrl_ns = data_out_clear_i ? CLEAR_S : CLEAR_KD; *)
          let key_clear_d = key_clear_i in
          let data_out_clear_d = data_out_clear_i in
          let aes_cipher_ctrl_ns = if data_out_clear_i then !CLEAR_S else !CLEAR_KD in
          ( aes_cipher_ctrl_ns
          , round_q
          , num_rounds_q
          , crypt_q
          , dec_key_gen_d
          , key_clear_d
          , data_out_clear_d
          )
        else if dec_key_gen_i || crypt_i then
          (* // Start encryption/decryption or generation of start key for decryption. *)
          (* crypt_d       = ~dec_key_gen_i; *)
          (* dec_key_gen_d =  dec_key_gen_i; *)

          (* // Load input data to state *)
          (* state_sel_o = dec_key_gen_d ? STATE_CLEAR : STATE_INIT; *)
          (* state_we_o  = 1'b1; *)

          (* // Init key expand *)
          (* key_expand_clear_o = 1'b1; *)

          (* // Load full key *)
          (* key_full_sel_o = dec_key_gen_d ? KEY_FULL_ENC_INIT : *)
          (*             (op_i == CIPH_FWD) ? KEY_FULL_ENC_INIT : *)
          (*                                  KEY_FULL_DEC_INIT; *)
          (* key_full_we_o  = 1'b1; *)

          (* // Load num_rounds, clear round *)
          (* round_d      = '0; *)
          (* num_rounds_d = (key_len_i == AES_128) ? 4'd10 : *)
          (*                (key_len_i == AES_192) ? 4'd12 : *)
          (*                                         4'd14; *)
          (* aes_cipher_ctrl_ns = INIT; *)
          let crypt_d            = not dec_key_gen_i in
          let dec_key_gen_d      = dec_key_gen_i in
          let round_d            = #0 in
          let num_rounds_d       = #14 in
          let aes_cipher_ctrl_ns = !INIT in
          ( aes_cipher_ctrl_ns
          , round_d
          , num_rounds_d
          , crypt_d
          , dec_key_gen_d
          , key_clear_q
          , data_out_clear_q
          )
        else state
      else state


    else if aes_cipher_ctrl_cs == !IDLE then
        (* INIT: begin *)
        (*   // Initial round: just add key to state *)
        (*   state_we_o   = ~dec_key_gen_q; *)
        (*   add_rk_sel_o = ADD_RK_INIT; *)

        (*   // Select key words for initial add_round_key *)
        (*   key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO : *)
        (*       (key_len_i == AES_128)                     ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_2345 : *)
        (*       (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_4567 : KEY_WORDS_ZERO; *)

        (*   // Make key expand advance - AES-256 has two round keys available right from beginning. *)
        (*   if (key_len_i != AES_256) begin *)
        (*     key_expand_step_o = 1'b1; *)
        (*     key_full_we_o     = 1'b1; *)
        (*   end *)

        (*   aes_cipher_ctrl_ns = ROUND; *)
        (* end *)
      state

    else if aes_cipher_ctrl_cs == !ROUND then
        (* ROUND: begin *)
        (*   // Normal rounds *)
        (*   state_we_o = ~dec_key_gen_q; *)

        (*   // Select key words for add_round_key *)
        (*   key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO : *)
        (*       (key_len_i == AES_128)                     ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 : *)
        (*       (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 : *)
        (*       (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO; *)

        (*   // Make key expand advance *)
        (*   key_expand_step_o = 1'b1; *)
        (*   key_full_we_o     = 1'b1; *)

        (*   // Select round key: direct or mixed (equivalent inverse cipher) *)
        (*   round_key_sel_o = (op_i == CIPH_FWD) ? ROUND_KEY_DIRECT : ROUND_KEY_MIXED; *)

        (*   // Update round *)
        (*   round_d = round_q + 4'b0001; *)

        (*   // Are we doing the last regular round? *)
        (*   if (round_q == num_rounds_regular) begin *)
        (*     aes_cipher_ctrl_ns = FINISH; *)

        (*     if (dec_key_gen_q) begin *)
        (*       // Write decryption key. *)
        (*       key_dec_we_o = 1'b1; *)

        (*       // Indicate that we are done, try to perform the handshake. But we don't wait here *)
        (*       // as the decryption key is valid only during one cycle. If we don't get the *)
        (*       // handshake now, we will wait in the finish state. *)
        (*       out_valid_o = 1'b1; *)
        (*       if (out_ready_i) begin *)
        (*         // Go to idle state directly. *)
        (*         dec_key_gen_d      = 1'b0; *)
        (*         aes_cipher_ctrl_ns = IDLE; *)
        (*       end *)
        (*     end *)
        (*   end *)
        (* end *)
      state

    else if aes_cipher_ctrl_cs == !FINISH then
        (* FINISH: begin *)
        (*   // Final round *)

        (*   // Select key words for add_round_key *)
        (*   key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO : *)
        (*       (key_len_i == AES_128)                     ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 : *)
        (*       (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 : *)
        (*       (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO; *)

        (*   // Skip mix_columns *)
        (*   add_rk_sel_o = ADD_RK_FINAL; *)

        (*   // Indicate that we are done, wait for handshake. *)
        (*   out_valid_o = 1'b1; *)
        (*   if (out_ready_i) begin *)
        (*     // We don't need the state anymore, clear it. *)
        (*     state_we_o         = 1'b1; *)
        (*     state_sel_o        = STATE_CLEAR; *)
        (*     crypt_d            = 1'b0; *)
        (*     // If we were generating the decryption key and didn't get the handshake in the last *)
        (*     // regular round, we should clear dec_key_gen now. *)
        (*     dec_key_gen_d      = 1'b0; *)
        (*     aes_cipher_ctrl_ns = IDLE; *)
        (*   end *)
        (* end *)
      state
    else if aes_cipher_ctrl_cs == !CLEAR_S then
        (* CLEAR_S: begin *)
        (*   // Clear the state with pseudo-random data. *)
        (*   state_we_o         = 1'b1; *)
        (*   state_sel_o        = STATE_CLEAR; *)
        (*   aes_cipher_ctrl_ns = CLEAR_KD; *)
        (* end *)
      state

    else (* if aes_cipher_ctrl_cs == !CLEAR_KD *)
        (* CLEAR_KD: begin *)
        (*   // Clear internal key registers and/or external data output registers. *)
        (*   if (key_clear_q) begin *)
        (*     key_full_sel_o = KEY_FULL_CLEAR; *)
        (*     key_full_we_o  = 1'b1; *)
        (*     key_dec_sel_o  = KEY_DEC_CLEAR; *)
        (*     key_dec_we_o   = 1'b1; *)
        (*   end *)
        (*   if (data_out_clear_q) begin *)
        (*     // Forward the state (previously cleared with psuedo-random data). *)
        (*     add_rk_sel_o    = ADD_RK_INIT; *)
        (*     key_words_sel_o = KEY_WORDS_ZERO; *)
        (*     round_key_sel_o = ROUND_KEY_DIRECT; *)
        (*   end *)
        (*   // Indicate that we are done, wait for handshake. *)
        (*   out_valid_o = 1'b1; *)
        (*   if (out_ready_i) begin *)
        (*     key_clear_d        = 1'b0; *)
        (*     data_out_clear_d   = 1'b0; *)
        (*     aes_cipher_ctrl_ns = IDLE; *)
        (*   end *)
        (* end *)
      state
  ]>.

