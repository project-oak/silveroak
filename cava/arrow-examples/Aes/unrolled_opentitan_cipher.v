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

(* Note: aes_key_expand in OpenTitan is stateful, this version is not *)
Program
Definition aes_key_expand
  (sbox_impl: SboxImpl)
  : << Bit (* op_i *)
    , Vector Bit 4 (* round id *)
    , Vector Bit 8 (* rcon input *)
    , Vector (Vector (Vector Bit 8) 4) 8 (* input key *)
    , Unit
    >> ~>
      << Vector Bit 8, Vector (Vector (Vector Bit 8) 4) 8>> :=
  <[\op_i round_id rcon key_i =>
    (* if (key_len_i == AES_256 && rnd[0] == 1'b0) begin
    use_rcon = 1'b0;
    end *)
    let use_rcon = round_id[#0] in
    let clear_i =
      round_id == #0 in

    (* rcon_d = (op_i == CIPH_FWD) ? aes_mul2(rcon_q) :
                (op_i == CIPH_INV) ? aes_div2(rcon_q) : 8'h01; *)
    let rcon_d =
      if clear_i
      then
        if op_i == !CIPH_FWD
        then #1
        else #64
      else
        if op_i == !CIPH_FWD
        then !aes_mul2 rcon
        else !aes_div2 rcon in

    (* AES_256: begin
      unique case (op_i)
        CIPH_FWD: rot_word_in = key_i[7];
        CIPH_INV: rot_word_in = key_i[3];
        default:  rot_word_in = key_i[7]; *)
    let rot_word_in =
      if op_i == !CIPH_FWD
      then key_i[#7]
      else key_i[#3] in

    (* assign rot_word_out = aes_circ_byte_shift(rot_word_in, 2'h3); *)
    let rot_word_out = !aes_circ_byte_shift rot_word_in #3 in

    (* assign sub_word_in = use_rot_word ? rot_word_out : rot_word_in; *)
    let sub_word_in =
      if use_rcon (* for AES_256 use_rcon == use_rot_word *)
      then rot_word_out
      else rot_word_in in

    let sub_word_out = !(map <[!(aes_sbox sbox_impl) !CIPH_FWD]>) sub_word_in in
    let sub_word_out_flat = !(flatten (n:=4)) sub_word_out in

    (* assign rcon_add_in  = sub_word_out[7:0]; *)
    let rcon_add_in = sub_word_out_flat[:7:0] in
    (* assign rcon_add_out = rcon_add_in ^ rcon_q; *)
    let rcon_add_out = rcon_add_in ^ rcon in
    (* assign rcon_added   = {sub_word_out[31:8], rcon_add_out}; *)
    let rcon_added   = concat rcon_add_out sub_word_out_flat[:31:8] in

    (* // Mux output coming from Rcon & SubWord
    assign irregular = use_rcon ? rcon_added : sub_word_out; *)
    let irregular = if use_rcon then rcon_added else sub_word_out_flat in

    (* AES_256: begin
        unique case (op_i)
          CIPH_FWD: begin
            if (rnd == 0) begin
              // Round 0: Nothing to be done
              // The Full Key registers are not updated
              regular = {key_i[3:0], key_i[7:4]};
            end else begin
              // Shift down old upper half
              regular[3:0] = key_i[7:4];
              // Generate new upper half
              regular[4]   = irregular ^ key_i[0];
              for (int i=1; i<4; i++) begin
                regular[i+4] = regular[i+4-1] ^ key_i[i];
              end
            end // rnd == 0
          end

        endcase
      end *)
    let regular =
      if round_id == #0
      then concat key_i[:7:4] key_i[:3:0]
      else
        if op_i == !CIPH_FWD
        then
          (* todo: this is a "scan" op *)
          let regular_4 = (!reshape irregular) ^ key_i[#0] in
          let regular_5 = regular_4 ^ key_i[#1] in
          let regular_6 = regular_5 ^ key_i[#2] in
          let regular_7 = regular_6 ^ key_i[#3] in
          snoc (snoc (snoc (snoc key_i[:7:4] regular_4) regular_5) regular_6) regular_7

          (* CIPH_INV: begin
            if (rnd == 0) begin
              // Round 0: Nothing to be done
              // The Full Key registers are not updated
              regular = {key_i[3:0], key_i[7:4]};
            end else begin
              // Shift up old lower half
              regular[7:4] = key_i[3:0];
              // Generate new lower half
              regular[0]   = irregular ^ key_i[4];
              for (int i=0; i<3; i++) begin
                regular[i+1] = key_i[4+i] ^ key_i[4+i+1];
              end
            end // rnd == 0
          end *)
        else
          let regular_0 = (!reshape irregular) ^ key_i[#4] in
          let regular_1 = key_i[#4] ^ key_i[#5] in
          let regular_2 = key_i[#5] ^ key_i[#6] in
          let regular_3 = key_i[#6] ^ key_i[#7] in
          cons regular_0 (cons regular_1 (cons regular_2 (cons regular_3 key_i[:3:0])))
      in
    (if (or use_rcon clear_i) then rcon_d else rcon, regular)
    ]>.

Definition key_expand_and_round
  (sbox_impl: SboxImpl)
  : <<
      << Bit
      , Vector Bit 8 (* rcon *)
      , Vector (Vector (Vector Bit 8) 4) 4 (* data *)
      , Vector (Vector (Vector Bit 8) 4) 8 (* key *)
      (* , Unit *)
      >>,
      Vector Bit 4, (* round *)
      Unit
    >> ~>
    << Bit
    , Vector Bit 8 (* rcon *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* data *)
    , Vector (Vector (Vector Bit 8) 4) 8 (* key *)
    (* , Unit *)
    >> :=
  <[\state round =>
    let '(op_i, state') = state in
    let '(rcon, state'') = state' in
    let '(data_i, key) = state'' in

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
      if round == #0 then
        data_i ^ key_words
      else
        !(cipher_round sbox_impl) op_i data_i round_key in

    let '(rcon', new_key) = !(aes_key_expand sbox_impl) op_i round rcon key in
    (op_i, rcon', data_o, new_key)
  ]>.

(* stateless *)
Definition unrolled_cipher
  (sbox_impl: SboxImpl)
  : << Bit
    , Vector (Vector (Vector Bit 8) 4) 4 (* data *)
    , Vector (Vector (Vector Bit 8) 4) 8 (* key *)
    , Unit
    >> ~>
    <<
      Vector (Vector (Vector Bit 8) 4) 4 (* data *)
    >>
      :=
  let cipher_round := cipher_round sbox_impl in
  let aes_key_expand := aes_key_expand sbox_impl in
  <[\op_i data_i key_i =>
    (* OpenTitan runs the AES cipher core forwards to generate the decryption
    keys. Since this is an unrolled variant we just duplicate the core logic *)
    let rcon_initial = #1 in
    let forward_keys = concat key_i[:7:4] key_i[:3:0] in

    let '(_, fwd_end_state) =
      !(foldl (n:=14) (key_expand_and_round sbox_impl))
      (!CIPH_FWD, rcon_initial, data_i, forward_keys) !(seq 0) in
    let '(data_i', key') = snd fwd_end_state in
    let forward_o = !(final_cipher_round sbox_impl) !CIPH_FWD data_i' (!aes_transpose key'[:7:4]) in

    let backward_keys = concat key'[:7:4] key'[:3:0] in

    let '(_, bkw_end_state) =
      !(foldl (n:=14) (key_expand_and_round sbox_impl))
      (!CIPH_INV, #64, data_i, backward_keys) !(seq 0) in
    let '(rev_data_i', rev_key) = snd bkw_end_state in
    let backward_o = !(final_cipher_round sbox_impl) !CIPH_INV rev_data_i' (!aes_transpose rev_key[:3:0]) in

    if op_i == !CIPH_FWD
    then forward_o
    else backward_o
    ]>.


Definition unrolled_cipher_flat
  (sbox_impl: SboxImpl)
  : << Bit
    , Vector Bit 128 (* data *)
    , Vector Bit 256 (* key *)
    , Unit
    >> ~>
    <<
      Vector Bit 128 (* data *)
    >>
      :=
  <[\op_i data key =>
    let data_o = !(unrolled_cipher sbox_impl) op_i (!aes_transpose (!reshape (!reshape data))) (!reshape (!reshape key)) in
    !flatten (!flatten (!aes_transpose data_o))
    ]>.

Section tests.
  From ArrowExamples Require Import Combinators Aes.aes_test.

  Definition unrolled_cipher' mode key data :=
    interp_combinational (unrolled_cipher_flat SboxCanright _) (mode,(data,key)).

  Definition unrolled_cipher_test_fwd := test_cipher_fwd unrolled_cipher'.
  Definition unrolled_cipher_value_fwd := print_cipher_fwd unrolled_cipher'.
  Definition unrolled_cipher_test_rev := test_cipher_rev unrolled_cipher'.
  Definition unrolled_cipher_value_rev := print_cipher_rev unrolled_cipher'.

End tests.
