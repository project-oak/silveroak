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

From ArrowExamples Require Import Combinators Aes.pkg Aes.sbox.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

Definition aes_mix_single_column
  :  
    <<Bit, Vector (Vector Bit 8) 4, Unit>> ~> 
      Vector (Vector Bit 8) 4 :=
  <[\ op_i data_i =>
  (* logic [3:0][7:0] x;
  logic [1:0][7:0] y;
  logic [1:0][7:0] z;

  logic [3:0][7:0] x_mul2;
  logic [1:0][7:0] y_pre_mul4;
  logic      [7:0] y2, y2_pre_mul2;

  logic [1:0][7:0] z_muxed;

  // Drive x
  assign x[0] = data_i[0] ^ data_i[3];
  assign x[1] = data_i[3] ^ data_i[2];
  assign x[2] = data_i[2] ^ data_i[1];
  assign x[3] = data_i[1] ^ data_i[0];*)
  let x =
    data_i[#0] ^ data_i[#3] ::
    data_i[#3] ^ data_i[#2] ::
    data_i[#2] ^ data_i[#1] ::
    data_i[#1] ^ data_i[#0] :: [] in
  (*
  // Mul2(x)
  for (genvar i = 0; i < 4; i++) begin : gen_x_mul2
    assign x_mul2[i] = aes_mul2(x[i]);
  end*)
  let x_mul2 = !(map aes_mul2) x in
  (*
  // Drive y_pre_mul4
  assign y_pre_mul4[0] = data_i[3] ^ data_i[1];
  assign y_pre_mul4[1] = data_i[2] ^ data_i[0];
  *)
  let y_pre_mul4 = 
    data_i[#3] ^ data_i[#1] ::
    data_i[#2] ^ data_i[#0] :: [] in
(*
  // Mul4(y_pre_mul4)
  for (genvar i = 0; i < 2; i++) begin : gen_mul4
    assign y[i] = aes_mul4(y_pre_mul4[i]);
  end*)
  let y = !(map aes_mul4) y_pre_mul4 in
  (*
  // Drive y2_pre_mul2
  assign y2_pre_mul2 = y[0] ^ y[1]; *)
  let y2_pre_mul2 = y[#0] ^ y[#1] in

  (*// Mul2(y)
  assign y2 = aes_mul2(y2_pre_mul2);*)
  let y2 = !aes_mul2 y2_pre_mul2 in

  (*// Drive z
  assign z[0] = y2 ^ y[0];
  assign z[1] = y2 ^ y[1];*)
  let z = y2 ^ y[#0] :: y2 ^ y[#1] :: [] in

  (*// Mux z
  assign z_muxed[0] = (op_i == CIPH_FWD) ? 8'b0 : z[0];
  assign z_muxed[1] = (op_i == CIPH_FWD) ? 8'b0 : z[1];*)
  let z_muxed = 
    if op_i == !CIPH_FWD then #0 else z[#0] ::
    if op_i == !CIPH_FWD then #0 else z[#1] ::
    [] in

  (*// Drive outputs
  assign data_o[0] = data_i[1] ^ x_mul2[3] ^ x[1] ^ z_muxed[1];
  assign data_o[1] = data_i[0] ^ x_mul2[2] ^ x[1] ^ z_muxed[0];
  assign data_o[2] = data_i[3] ^ x_mul2[1] ^ x[3] ^ z_muxed[1];
  assign data_o[3] = data_i[2] ^ x_mul2[0] ^ x[3] ^ z_muxed[0]; *)
  data_i[#1] ^ x_mul2[#3] ^ x[#1] ^ z_muxed[#1] ::
  data_i[#0] ^ x_mul2[#2] ^ x[#1] ^ z_muxed[#0] ::
  data_i[#3] ^ x_mul2[#1] ^ x[#3] ^ z_muxed[#1] ::
  data_i[#2] ^ x_mul2[#0] ^ x[#3] ^ z_muxed[#0] :: []
  ]>.