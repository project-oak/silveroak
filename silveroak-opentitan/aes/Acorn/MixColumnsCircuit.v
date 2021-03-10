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

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.

Require Import Cava.Cava.
Require Import Cava.Cava.
Require Import Cava.Lib.BitVectorOps.
Require Import Cava.Lib.Multiplexers.
Require Import AcornAes.Pkg.

Local Notation byte := (Vec Bit 8) (only parsing).
Local Notation "v [@ n ]" := (indexConst v n) (at level 1, format "v [@ n ]").

Section WithCava.
  Context {signal} {semantics : Cava signal}.

  Definition aes_mix_single_column
    (op_i: signal Bit) (data_i: signal (Vec byte 4))
    : cava (signal (Vec byte 4)) :=
    (*
    //
    // AES MixColumns for one single column of the state matrix
    //
    // For details, see Equations 4-7 of:
    // Satoh et al., "A Compact Rijndael Hardware Architecture with S-Box Optimization"
     *)

    (* Get separate bytes from the input column *)
    data_i_0 <- data_i[@0] ;;
    data_i_1 <- data_i[@1] ;;
    data_i_2 <- data_i[@2] ;;
    data_i_3 <- data_i[@3] ;;

    (* // Drive x *)
    (* assign x[0] = data_i[0] ^ data_i[3]; *)
    (* assign x[1] = data_i[3] ^ data_i[2]; *)
    (* assign x[2] = data_i[2] ^ data_i[1]; *)
    (* assign x[3] = data_i[1] ^ data_i[0]; *)
    x_0 <- xorV (data_i_0, data_i_3) ;;
    x_1 <- xorV (data_i_3, data_i_2) ;;
    x_2 <- xorV (data_i_2, data_i_1) ;;
    x_3 <- xorV (data_i_1, data_i_0) ;;


    (* // Mul2(x) *)
    (*   for (genvar i = 0; i < 4; i++) begin : gen_x_mul2 *)
    (*     assign x_mul2[i] = aes_mul2(x[i]); *)
    (*   end *)
    x_mul2_0 <- aes_mul2 x_0 ;;
    x_mul2_1 <- aes_mul2 x_1 ;;
    x_mul2_2 <- aes_mul2 x_2 ;;
    x_mul2_3 <- aes_mul2 x_3 ;;

    (* // Drive y_pre_mul4 *)
    (* assign y_pre_mul4[0] = data_i[3] ^ data_i[1]; *)
    (* assign y_pre_mul4[1] = data_i[2] ^ data_i[0]; *)
    y_pre_mul4_0 <- xorv data_i_3 data_i_1 ;;
    y_pre_mul4_1 <- xorv data_i_2 data_i_0 ;;
    (* // Mul4(y_pre_mul4) *)
    (* for (genvar i = 0; i < 2; i++) begin : gen_mul4 *)
    (*   assign y[i] = aes_mul4(y_pre_mul4[i]); *)
    (* end *)
    y_0 <- aes_mul4 y_pre_mul4_0 ;;
    y_1 <- aes_mul4 y_pre_mul4_1 ;;

    (* // Drive y2_pre_mul2 *)
    (* assign y2_pre_mul2 = y[0] ^ y[1]; *)
    y2_pre_mul2 <- xorv y_0 y_1 ;;
    (* // Mul2(y) *)
    (* assign y2 = aes_mul2(y2_pre_mul2); *)
    y2 <- aes_mul2 y2_pre_mul2 ;;

    (* // Drive z *)
    (* assign z[0] = y2 ^ y[0]; *)
    (* assign z[1] = y2 ^ y[1]; *)
    z_0 <- xorv y2 y_0 ;;
    z_1 <- xorv y2 y_1 ;;

    (* // Mux z *)
    (* assign z_muxed[0] = (op_i == CIPH_FWD) ? 8'b0 : z[0]; *)
    (* assign z_muxed[1] = (op_i == CIPH_FWD) ? 8'b0 : z[1]; *)
    zero_byte <- zero_byte ;;
    z_muxed_0 <- mux2 op_i (zero_byte, z_0) ;;
    z_muxed_1 <- mux2 op_i (zero_byte, z_1) ;;

    (* // Drive outputs *)
    (* assign data_o[0] = data_i[1] ^ x_mul2[3] ^ x[1] ^ z_muxed[1]; *)
    (* assign data_o[1] = data_i[0] ^ x_mul2[2] ^ x[1] ^ z_muxed[0]; *)
    (* assign data_o[2] = data_i[3] ^ x_mul2[1] ^ x[3] ^ z_muxed[1]; *)
    (* assign data_o[3] = data_i[2] ^ x_mul2[0] ^ x[3] ^ z_muxed[0]; *)
    data_o0 <- (xorv data_i_1 x_mul2_3 >>= xorv x_1 >>= xorv z_muxed_1) ;;
    data_o1 <- (xorv data_i_0 x_mul2_2 >>= xorv x_1 >>= xorv z_muxed_0) ;;
    data_o2 <- (xorv data_i_3 x_mul2_1 >>= xorv x_3 >>= xorv z_muxed_1) ;;
    data_o3 <- (xorv data_i_2 x_mul2_0 >>= xorv x_3 >>= xorv z_muxed_0) ;;

    packV [data_o0; data_o1; data_o2; data_o3].

  Definition aes_mix_columns
             (op_i : signal Bit)
    : signal (Vec (Vec (Vec Bit 8) 4) 4)
      -> cava (signal (Vec (Vec (Vec Bit 8) 4) 4)) :=
    (* // Transpose to operate on columns
    logic [3:0][3:0][7:0] data_i_transposed;
    logic [3:0][3:0][7:0] data_o_transposed;

    assign data_i_transposed = aes_transpose(data_i);

    // Individually mix columns
    for (genvar i = 0; i < 4; i++) begin : gen_mix_column
      aes_mix_single_column aes_mix_column_i (
        .op_i   ( op_i                 ),
        .data_i ( data_i_transposed[i] ),
        .data_o ( data_o_transposed[i] )
      );
    end

    assign data_o = aes_transpose(data_o_transposed); *)
    aes_transpose >=> Vec.map (aes_mix_single_column op_i)
                  >=> aes_transpose.

End WithCava.
