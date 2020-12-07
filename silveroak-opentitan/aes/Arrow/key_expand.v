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

Require Import Coq.Arith.Arith Coq.Vectors.Vector
     Coq.NArith.NArith.
Require Import Cava.Arrow.ArrowExport.

Require Import Aes.pkg Aes.sbox.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

Program Definition aes_key_expand
  (sbox_impl: SboxImpl)
  : <<
   (* Bit (1* cfg_valid_i *1) *) (*cfg_valid_i is used for gating assertions only. *)
      Bit (* op_i *)
    , Bit (* step_i *)
    , Bit (* clear_i *)
    , Vector Bit 4 (* round_i *)
    (* , Vector Bit 4 (1* key_len_e *1) *)
    , Vector (Vector (Vector Bit 8) 4) 8 (* input key *)
    , Unit
    >> ~> << Vector (Vector (Vector Bit 8) 4) 8>> :=
  <[\op_i step_i clear_i round_i key_i =>
    (* if (key_len_i == AES_256 && rnd[0] == 1'b0) begin
    use_rcon = 1'b0;
    end *)
    let use_rcon = round_i[#0] in
    let clear_i =
      round_i == #0 in

    (* rcon_d = (op_i == CIPH_FWD) ? aes_mul2(rcon_q) :
                (op_i == CIPH_INV) ? aes_div2(rcon_q) : 8'h01; *)
    letrec rcon = delay (
      if clear_i
      then
        if op_i == !CIPH_FWD
        then #1
        else #64
      else if use_rcon
      then
        if op_i == !CIPH_FWD
        then !aes_mul2 rcon
        else !aes_div2 rcon
      else
        rcon
        ) in

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
      if round_i == #0
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
    regular
    ]>.
