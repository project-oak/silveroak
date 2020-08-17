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

From ArrowExamples Require Import Combinators Aes.pkg Aes.mix_columns Aes.sbox Aes.sub_bytes Aes.shift_rows.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

Definition cipher_round
  (sbox_impl: SboxImpl)
  : forall cava: Cava,
    << Bit                               (* cipher mode: CIPH_FWD/CIPH_INV *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* data input *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* round key *)
    , Unit>> ~>
      Vector (Vector (Vector Bit 8) 4) 4 :=
  <[\op_i data_i stage_key =>
    let stage1 = !(aes_sub_bytes sbox_impl) op_i data_i in
    let stage2 = !aes_shift_rows op_i stage1 in
    let stage3 = !aes_mix_columns op_i stage2 in
    !(map2 <[ !(map2 <[\x y => x ^ y]>) ]> ) stage3 stage_key
    ]>.

(* Note: aes_key_expand in OpenTitan is stateful, this version is not *)
Program Definition aes_key_expand
  (sbox_impl: SboxImpl)
  : forall cava: Cava,
    << Bit (* op_i *)
    , Vector Bit 3 (* round id *)
    , Vector Bit 8 (* rcon input *)
    , Vector (Vector (Vector Bit 8) 4) 8 (* input key *)
    , Unit
    >> ~>
      << Vector Bit 8, Vector (Vector (Vector Bit 8) 4) 8>> :=
  let sbox := curry (aes_sbox sbox_impl) in
  let mapped_sbox := <[ !(map sbox) ]> in
  <[\op_i round_id rcon key_i =>
    (* if (key_len_i == AES_256 && rnd[0] == 1'b0) begin
    use_rcon = 1'b0;
    end *)
    let use_rcon = round_id[#0] in

    (* rcon_d = (op_i == CIPH_FWD) ? aes_mul2(rcon_q) :
                (op_i == CIPH_INV) ? aes_div2(rcon_q) : 8'h01; *)
    let rcon =
      if round_id == #0
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

    let sub_word_out = !mapped_sbox (!(map2 <[\x y => (x,y)]>) (!replicate op_i) sub_word_in) in
    let sub_word_out_flat = !flatten sub_word_out in

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
    (rcon, regular)
    ]>.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.

Program Definition key_expand_and_round
  (sbox_impl: SboxImpl)
  : forall cava: Cava,
    <<
      <<
        Vector Bit 8 (* rcon *)
      , Vector (Vector (Vector Bit 8) 4) 4 (* data *)
      , Vector (Vector (Vector Bit 8) 4) 8 (* key *)
      (* , Unit *)
      >>,
      Vector Bit 3, (* round *)
      Unit
    >> ~>
    <<
      Vector Bit 8 (* rcon *)
    , Vector (Vector (Vector Bit 8) 4) 4 (* data *)
    , Vector (Vector (Vector Bit 8) 4) 8 (* key *)
    (* , Unit *)
    >> :=
  <[\state round =>
    let '(rcon, state') = state in
    let '(data_i, key) = state' in

    let key_words_0 = key[:3:0] in
    let key_bytes_0 = !aes_transpose key_words_0 in
    let round_key = key_bytes_0 in

    let '(rcon', new_key) = !(aes_key_expand sbox_impl) !CIPH_FWD round rcon key in
    let data_o = !(cipher_round sbox_impl) !CIPH_FWD data_i round_key in
    (rcon', data_o, new_key)
  ]>.
Next Obligation. lia. Qed.

(* stateless *)
Program Definition unrolled_forward_cipher
  (sbox_impl: SboxImpl)
  : forall cava: Cava,
    <<
      (* Vector Bit 8 *)
      Vector (Vector (Vector Bit 8) 4) 4 (* data *)
    , Vector (Vector (Vector Bit 8) 4) 8 (* key *)
    , Unit
    >> ~>
    <<
      (* Vector Bit 8 rcon *)
      Vector (Vector (Vector Bit 8) 4) 4 (* data *)
    (* , Vector (Vector (Vector Bit 8) 4) 8 *)
    >>
      :=
  let cipher_round := cipher_round sbox_impl in
  let aes_key_expand := aes_key_expand sbox_impl in
  <[\data_i key =>
    let rcon = #1 in

    let '(rcon, end_state) = !(foldl (n:=13) (key_expand_and_round sbox_impl)) (rcon, data_i, key) !(seq (n:=13) 0) in
    let '(data_i, key) = end_state in


    (* final round has no mix_columns *)
    let '(_, key) = !aes_key_expand !CIPH_FWD #13 rcon key in

    let key_words_0 = key[:3:0] in
    let key_bytes_0 = !aes_transpose key_words_0 in
    let round_key = key_bytes_0 in

    let stage1 = !(aes_sub_bytes sbox_impl) !CIPH_FWD data_i in
    let stage2 = !aes_shift_rows !CIPH_FWD stage1 in
    !(map2 <[ !(map2 <[\x y => x ^ y]>) ]> ) stage2 round_key
    ]>.
Next Obligation. lia. Qed.

Definition unrolled_forward_cipher_flat
  : forall cava: Cava,
    <<
      Vector Bit 128 (* data *)
    , Vector Bit 256 (* key *)
    , Unit
    >> ~>
    <<
      Vector Bit 128 (* data *)
    (* , Vector Bit 256 *)
    >>
      :=
  <[\data key =>
    let data_o = !(unrolled_forward_cipher SboxCanright) (!reshape (!reshape data)) (!reshape (!reshape key)) in
    !flatten (!flatten data_o)
    ]>.

Definition test_key := N2Bv_sized 256 0.

(* 0x80000000000000000000000000000000 *)
Definition test_data := N2Bv_sized 128 170141183460469231731687303715884105728.

(* 0xddc6bf790c15760d8d9aeb6f9a75fd4e *)
Definition test_encrypted := N2Bv_sized 128 294791345377038030526550647723007540558.

Definition eval_unrolled : nat := bitvec_to_nat (unrolled_forward_cipher_flat Combinational (test_data, (test_key, tt))).