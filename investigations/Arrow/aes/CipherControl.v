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

From Coq Require Import Arith.Arith Logic.Eqdep_dec Vectors.Vector micromega.Lia
     NArith.NArith Strings.String NArith.Ndigits.
From Cava Require Import Arrow.ArrowExport BitArithmetic.

Require Import Aes.Pkg Aes.MixColumns Aes.Sbox Aes.SubBytes Aes.ShiftRows Aes.CipherRound.

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

Definition aes_cipher_control_output :=
  (* output logic                    in_ready_o, *)
  << Bit
  (* // Output handshake signals *)
  (* output logic                    out_valid_o, *)
  , Bit
  (* // Control and sync signals *)
  (* output logic                    crypt_o, *)
  , Bit
  (* output logic                    dec_key_gen_o, *)
  , Bit
  (* output logic                    key_clear_o, *)
  , Bit
  (* output logic                    data_out_clear_o, *)
  , Bit
  (* // Control outputs cipher data path *)
  (* output aes_pkg::state_sel_e     state_sel_o, *)
  , state_sel_e
  (* output logic                    state_we_o, *)
  , Bit
  (* output aes_pkg::add_rk_sel_e    add_rk_sel_o, *)
  , add_rk_sel_e
  (* // Control outputs key expand data path *)
  (* output aes_pkg::ciph_op_e       key_expand_op_o, *)
  , ciph_op_e
  (* output aes_pkg::key_full_sel_e  key_full_sel_o, *)
  , key_full_sel_e
  (* output logic                    key_full_we_o, *)
  , Bit
  (* output aes_pkg::key_dec_sel_e   key_dec_sel_o, *)
  , key_dec_sel_e
  (* output logic                    key_dec_we_o, *)
  , Bit
  (* output logic                    key_expand_step_o, *)
  , Bit
  (* output logic                    key_expand_clear_o, *)
  , Bit
  (* output logic [3:0]              key_expand_round_o, *)
  , Vector Bit 4
  (* output aes_pkg::key_words_sel_e key_words_sel_o, *)
  , key_words_sel_e
  (* output aes_pkg::round_key_sel_e round_key_sel_o *)
  , round_key_sel_e
  >>.

(* TODO: typechecking hangs on the below definition *)
(*
Definition aes_cipher_control_transition
  : << aes_cipher_control_state, aes_cipher_control_input, Unit>>
  ~> <<aes_cipher_control_state, aes_cipher_control_output>>
  :=
  <[ \ state input =>
    let '( aes_cipher_ctrl_cs
         , round_q
         , num_rounds_q
         , crypt_q
         , dec_key_gen_q
         , key_clear_q
         , data_out_clear_q
         ) : aes_cipher_control_state = state in

    let '( in_valid_i
         , out_ready_i
         , op_i
         , crypt_i
         , dec_key_gen_i
         , key_clear_i
         , data_out_clear_i
         ) : aes_cipher_control_input = input in

    (* // Use separate signal for number of regular rounds. *)
    (* assign num_rounds_regular = num_rounds_q - 4'd2; *)
    let num_rounds_regular = num_rounds_q - #2 in

    (* // Handshake signals *)
    let in_ready_o         = false' in
    let out_valid_o        = false' in
    let default_io_o =
      ( in_ready_o
      , out_valid_o) in

    (* // Cipher data path *)
    let state_sel_o        = !STATE_ROUND in
    let state_we_o         = false' in
    let add_rk_sel_o       = !ADD_RK_ROUND in
    let default_state_o =
      ( !STATE_ROUND
      , false'
      , !ADD_RK_ROUND) in

    (* // Key expand data path *)
    let key_full_sel_o     = !KEY_FULL_ROUND in
    let key_full_we_o      = false' in
    let key_dec_sel_o      = !KEY_DEC_EXPAND in
    let key_dec_we_o       = false' in
    let key_expand_step_o  = false' in
    let key_expand_clear_o = false' in
    let key_words_sel_o    = !KEY_WORDS_ZERO in
    let round_key_sel_o    = !ROUND_KEY_DIRECT in

    let default_key_o =
      ( key_full_sel_o
      , key_full_we_o
      , key_dec_sel_o
      , key_dec_we_o
      , key_expand_step_o
      , key_expand_clear_o
      , key_words_sel_o
      , round_key_sel_o) in

    let '(next_state, io_o, state_o, key_o) =
      if aes_cipher_ctrl_cs == !IDLE then
        (* IDLE: begin *)
        (*   dec_key_gen_d = 1'b0; *)
        let dec_key_gen_d = false' in
        (*   // Signal that we are ready, wait for handshake. *)
        (*   in_ready_o = 1'b1; *)
        let in_ready_o = true' in

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

            ( ( aes_cipher_ctrl_ns
              , round_q
              , num_rounds_q
              , crypt_q
              , dec_key_gen_d
              , key_clear_d
              , data_out_clear_d
              )
            , default_io_o, default_state_o, default_key_o
            )
          else if (dec_key_gen_i || crypt_i) then
            (* // Start encryption/decryption or generation of start key for decryption. *)
            (* crypt_d       = ~dec_key_gen_i; *)
            (* dec_key_gen_d =  dec_key_gen_i; *)
            let crypt_d            = not dec_key_gen_i in
            let dec_key_gen_d      = dec_key_gen_i in

            (* // Load input data to state *)
            (* state_sel_o = dec_key_gen_d ? STATE_CLEAR : STATE_INIT; *)
            (* state_we_o  = 1'b1; *)
            let state_sel_o  = if dec_key_gen_d then !STATE_CLEAR else !STATE_INIT in
            let state_we_o = true' in

            (* // Init key expand *)
            (* key_expand_clear_o = 1'b1; *)
            let key_expand_clear_o = true' in

            (* // Load full key *)
            (* key_full_sel_o = dec_key_gen_d ? KEY_FULL_ENC_INIT : *)
            (*             (op_i == CIPH_FWD) ? KEY_FULL_ENC_INIT : *)
            (*                                  KEY_FULL_DEC_INIT; *)
            (* key_full_we_o  = 1'b1; *)
            let key_full_sel_o =
              if dec_key_gen_d then !KEY_FULL_ENC_INIT
              else
                if op_i == !CIPH_FWD then !KEY_FULL_ENC_INIT
                else !KEY_FULL_DEC_INIT in
            let key_full_we_o = true' in

            (* // Load num_rounds, clear round *)
            (* round_d      = '0; *)
            (* num_rounds_d = (key_len_i == AES_128) ? 4'd10 : *)
            (*                (key_len_i == AES_192) ? 4'd12 : *)
            (*                                         4'd14; *)
            (* aes_cipher_ctrl_ns = INIT; *)
            let round_d            = #0 in
            let num_rounds_d       = #14 in
            let aes_cipher_ctrl_ns = !INIT in

            ( ( aes_cipher_ctrl_ns
              , round_d
              , num_rounds_d
              , crypt_d
              , dec_key_gen_d
              , key_clear_q
              , data_out_clear_q
              )
            , default_io_o
            , ( state_sel_o
              , state_we_o
              , add_rk_sel_o
              )
            , ( key_full_sel_o
              , key_full_we_o
              , key_dec_sel_o
              , key_dec_we_o
              , key_expand_step_o
              , key_expand_clear_o
              , key_words_sel_o
              , round_key_sel_o
            ) )

          else (state, default_io_o, default_state_o, default_key_o)
        else (state, default_io_o, default_state_o, default_key_o)
      else if aes_cipher_ctrl_cs == !INIT then
        (* INIT: begin *)
        (*   // Initial round: just add key to state *)
        (*   state_we_o   = ~dec_key_gen_q; *)
        let state_we_o = not dec_key_gen_q in
        (*   add_rk_sel_o = ADD_RK_INIT; *)
        let add_rk_sel_o = !ADD_RK_INIT in

        (*   // Select key words for initial add_round_key *)
        (*   key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO : *)
        (*       (key_len_i == AES_128)                     ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_2345 : *)
        (*       (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_0123 : *)
        (*       (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_4567 : KEY_WORDS_ZERO; *)
        let key_words_sel_o =
          if dec_key_gen_q then !KEY_WORDS_ZERO
          else
            (* key_len_i == AES_256 *)
            if op_i == !CIPH_FWD then !KEY_WORDS_0123
            else if op_i == !CIPH_INV then !KEY_WORDS_4567
            else !KEY_WORDS_ZERO in

        (*   // Make key expand advance - AES-256 has two round keys available right from beginning. *)
        (*   if (key_len_i != AES_256) begin *)
        (*     key_expand_step_o = 1'b1; *)
        (*     key_full_we_o     = 1'b1; *)
        (*   end *)
        let key_expand_step_o = true' in
        let key_full_we_o = true' in

        (*   aes_cipher_ctrl_ns = ROUND; *)
        (* end *)
        let aes_cipher_ctrl_ns = !ROUND in

        ( ( aes_cipher_ctrl_ns
          , round_q
          , num_rounds_q
          , crypt_q
          , dec_key_gen_q
          , key_clear_q
          , data_out_clear_q
          )
        , default_io_o
        , ( state_sel_o
          , state_we_o
          , add_rk_sel_o
          )
        , ( key_full_sel_o
          , key_full_we_o
          , key_dec_sel_o
          , key_dec_we_o
          , key_expand_step_o
          , key_expand_clear_o
          , key_words_sel_o
          , round_key_sel_o
        ) )

      else if aes_cipher_ctrl_cs == !ROUND then
          (* ROUND: begin *)
          (*   // Normal rounds *)
          (*   state_we_o = ~dec_key_gen_q; *)
        let state_we_o = not dec_key_gen_q in

          (*   // Select key words for add_round_key *)
          (*   key_words_sel_o = dec_key_gen_q                ? KEY_WORDS_ZERO : *)
          (*       (key_len_i == AES_128)                     ? KEY_WORDS_0123 : *)
          (*       (key_len_i == AES_192 && op_i == CIPH_FWD) ? KEY_WORDS_2345 : *)
          (*       (key_len_i == AES_192 && op_i == CIPH_INV) ? KEY_WORDS_0123 : *)
          (*       (key_len_i == AES_256 && op_i == CIPH_FWD) ? KEY_WORDS_4567 : *)
          (*       (key_len_i == AES_256 && op_i == CIPH_INV) ? KEY_WORDS_0123 : KEY_WORDS_ZERO; *)
        let key_words_sel_o =
          if dec_key_gen_q then !KEY_WORDS_ZERO
          else
            (* key_len_i == AES_256 *)
            if op_i == !CIPH_FWD then !KEY_WORDS_4567
            else if op_i == !CIPH_INV then !KEY_WORDS_0123
            else !KEY_WORDS_ZERO in

          (*   // Make key expand advance *)
          (*   key_expand_step_o = 1'b1; *)
          (*   key_full_we_o     = 1'b1; *)
        let key_expand_step_o = true' in
        let key_full_we_o = true' in

          (*   // Select round key: direct or mixed (equivalent inverse cipher) *)
          (*   round_key_sel_o = (op_i == CIPH_FWD) ? ROUND_KEY_DIRECT : ROUND_KEY_MIXED; *)
        let round_key_sel_o = if (op_i == !CIPH_FWD) then !ROUND_KEY_DIRECT else !ROUND_KEY_MIXED in

          (*   // Update round *)
          (*   round_d = round_q + 4'b0001; *)
        let round_d = round_q +% #1 in

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
        let key_dec_we_o =
          if (round_q == num_rounds_regular) && dec_key_gen_q
          then true'
          else false' in
        let out_valid_o = key_dec_we_o in

        let aes_cipher_ctrl_ns =
          if (round_q == num_rounds_regular)
          then
            if dec_key_gen_q && out_ready_i
            then !IDLE
            else !FINISH
          else aes_cipher_ctrl_cs in
        let dec_key_gen_d =
          if (round_q == num_rounds_regular) && dec_key_gen_q && out_ready_i
          then false'
          else dec_key_gen_q in

        ( ( aes_cipher_ctrl_ns
          , round_d
          , num_rounds_q
          , crypt_q
          , dec_key_gen_d
          , key_clear_q
          , data_out_clear_q
          )
        , default_io_o
        , ( state_sel_o
          , state_we_o
          , add_rk_sel_o
          )
        , ( key_full_sel_o
          , key_full_we_o
          , key_dec_sel_o
          , key_dec_we_o
          , key_expand_step_o
          , key_expand_clear_o
          , key_words_sel_o
          , round_key_sel_o
        ) )
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
        let key_words_sel_o =
          if dec_key_gen_q then !KEY_WORDS_ZERO
          else
            (* key_len_i == AES_256 *)
            if op_i == !CIPH_FWD then !KEY_WORDS_4567
            else if op_i == !CIPH_INV then !KEY_WORDS_0123
            else !KEY_WORDS_ZERO in

          (*   // Skip mix_columns *)
          (*   add_rk_sel_o = ADD_RK_FINAL; *)
        let add_rk_sel_o = !ADD_RK_FINAL in
        let out_valid_o = true' in

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
        if (out_ready_i)
        then
          ( ( !IDLE
            , round_q
            , num_rounds_q
            , crypt_q
            , false'
            , key_clear_q
            , data_out_clear_q
            )
          , ( in_ready_o
            , out_valid_o
            )
          , ( !STATE_CLEAR
            , true'
            , add_rk_sel_o
            )
          , ( key_full_sel_o
            , key_full_we_o
            , key_dec_sel_o
            , key_dec_we_o
            , key_expand_step_o
            , key_expand_clear_o
            , key_words_sel_o
            , round_key_sel_o
          ) )
        else
          ( state
          , ( in_ready_o
            , out_valid_o
            )
          , ( state_sel_o
            , state_we_o
            , add_rk_sel_o
            )
          , ( key_full_sel_o
            , key_full_we_o
            , key_dec_sel_o
            , key_dec_we_o
            , key_expand_step_o
            , key_expand_clear_o
            , key_words_sel_o
            , round_key_sel_o
          ) )
      else if aes_cipher_ctrl_cs == !CLEAR_S then
          (* CLEAR_S: begin *)
          (*   // Clear the state with pseudo-random data. *)
          (*   state_we_o         = 1'b1; *)
          (*   state_sel_o        = STATE_CLEAR; *)
          (*   aes_cipher_ctrl_ns = CLEAR_KD; *)
          (* end *)
        ( ( !CLEAR_KD
          , round_q
          , num_rounds_q
          , crypt_q
          , dec_key_gen_q
          , key_clear_q
          , data_out_clear_q
          )
        , default_io_o
        , ( !STATE_CLEAR
          , true'
          , add_rk_sel_o
          )
        , default_key_o
        )
      else (* if aes_cipher_ctrl_cs == !CLEAR_KD *)
          (* CLEAR_KD: begin *)
          (*   // Clear internal key registers and/or external data output registers. *)
          (*   if (key_clear_q) begin *)
          (*     key_full_sel_o = KEY_FULL_CLEAR; *)
          (*     key_full_we_o  = 1'b1; *)
          (*     key_dec_sel_o  = KEY_DEC_CLEAR; *)
          (*     key_dec_we_o   = 1'b1; *)
          (*   end *)
        let
          '(key_full_sel_o
          , key_full_we_o
          , key_dec_sel_o
          , key_dec_we_o) =
            if key_clear_q
            then (!KEY_FULL_CLEAR, true', !KEY_DEC_CLEAR, true')
            else (key_full_sel_o, key_full_we_o, key_dec_sel_o, key_dec_we_o)
            in
          (*   if (data_out_clear_q) begin *)
          (*     // Forward the state (previously cleared with psuedo-random data). *)
          (*     add_rk_sel_o    = ADD_RK_INIT; *)
          (*     key_words_sel_o = KEY_WORDS_ZERO; *)
          (*     round_key_sel_o = ROUND_KEY_DIRECT; *)
          (*   end *)
        let
          '(add_rk_sel_o
          , key_words_sel_o
          , round_key_sel_o) =
            if data_out_clear_q
            then (!ADD_RK_INIT, !KEY_WORDS_ZERO, !ROUND_KEY_DIRECT)
            else (add_rk_sel_o, key_words_sel_o, round_key_sel_o)
            in
          (*   // Indicate that we are done, wait for handshake. *)
          (*   out_valid_o = 1'b1; *)
        let out_valid_o = true' in
          (*   if (out_ready_i) begin *)
          (*     key_clear_d        = 1'b0; *)
          (*     data_out_clear_d   = 1'b0; *)
          (*     aes_cipher_ctrl_ns = IDLE; *)
          (*   end *)
          (* end *)

        let state_n =
          if (out_ready_i)
          then
            ( !IDLE
            , round_q
            , num_rounds_q
            , crypt_q
            , dec_key_gen_q
            , false'
            , false'
            )
          else state
        in
        ( state_n
        , ( in_ready_o
          , out_valid_o
          )
        , ( state_sel_o
          , state_we_o
          , add_rk_sel_o
          )
        , ( key_full_sel_o
          , key_full_we_o
          , key_dec_sel_o
          , key_dec_we_o
          , key_expand_step_o
          , key_expand_clear_o
          , key_words_sel_o
          , round_key_sel_o
        ) )
          in

    let '( _
         , round_d
         , _
         , _
         , dec_key_gen_d
         , _
         , _
         ) : aes_cipher_control_state = state in

    let '(in_ready_o, out_valid_o) = io_o in
    let '(state_sel_o, state_we_o, add_rk_sel_o) = state_o in
    let
      '( key_full_sel_o
      , key_full_we_o
      , key_dec_sel_o
      , key_dec_we_o
      , key_expand_step_o
      , key_expand_clear_o
      , key_words_sel_o
      , round_key_sel_o
      ) :
      << key_full_sel_e
      , Bit
      , key_dec_sel_e
      , Bit
      , Bit
      , Bit
      , key_words_sel_e
      , round_key_sel_e
      >>
      = key_o in

    (* // Use separate signals for key expand operation and round. *)
    (* assign key_expand_op_o    = (dec_key_gen_d || dec_key_gen_q) ? CIPH_FWD : op_i; *)
    (* assign key_expand_round_o = round_d; *)
    let key_expand_op_o    = if (dec_key_gen_d || dec_key_gen_q) then !CIPH_FWD else op_i in
    let key_expand_round_o = round_d in

    (* // Let the main controller know whate we are doing. *)
    (* assign crypt_o          = crypt_q; *)
    (* assign dec_key_gen_o    = dec_key_gen_q; *)
    (* assign key_clear_o      = key_clear_q; *)
    (* assign data_out_clear_o = data_out_clear_q; *)
    let crypt_o          = crypt_q in
    let dec_key_gen_o    = dec_key_gen_q in
    let key_clear_o      = key_clear_q in
    let data_out_clear_o = data_out_clear_q in

    (state,
      ( in_ready_o
      , out_valid_o
      , crypt_o
      , dec_key_gen_o
      , key_clear_o
      , data_out_clear_o
      , state_sel_o
      , state_we_o
      , add_rk_sel_o
      , key_expand_op_o
      , key_full_sel_o
      , key_full_we_o
      , key_dec_sel_o
      , key_dec_we_o
      , key_expand_step_o
      , key_expand_clear_o
      , key_expand_round_o
      , key_words_sel_o
      , round_key_sel_o)
    )
  ]>.


Definition aes_cipher_control
  : <<aes_cipher_control_input, Unit>> ~> <<aes_cipher_control_output>>
  := <[\x => !(mealy_machine aes_cipher_control_transition) x]>.
*)
