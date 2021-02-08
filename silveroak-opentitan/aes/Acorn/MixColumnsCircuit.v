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

Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Vectors.Vector.
Require Import Coq.NArith.Ndigits.
Require Import Coq.NArith.BinNat.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.

Require Import Cava.Cava.
Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.BitVectorOps.
Require Import AcornAes.Pkg.
Require Import AesSpec.Tests.Common.
Import Pkg.Notations.

Import VectorNotations.

Require Import AesSpec.AES256.

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

    (* // Drive x *)
    (* assign x[0] = data_i[0] ^ data_i[3]; *)
    (* assign x[1] = data_i[3] ^ data_i[2]; *)
    (* assign x[2] = data_i[2] ^ data_i[1]; *)
    (* assign x[3] = data_i[1] ^ data_i[0]; *)
    let x :=
      (data_i[@0], data_i[@3]) ::
      (data_i[@3], data_i[@2]) ::
      (data_i[@2], data_i[@1]) ::
      (data_i[@1], data_i[@0]) :: [] in
    x <- mapT xorV x ;;

    (* // Mul2(x) *)
    (*   for (genvar i = 0; i < 4; i++) begin : gen_x_mul2 *)
    (*     assign x_mul2[i] = aes_mul2(x[i]); *)
    (*   end *)
    x_mul2 <- mapT aes_mul2 x ;;
    let x := unpeel x in
    let x_mul2 := unpeel x_mul2 in

    (* // Drive y_pre_mul4 *)
    (* assign y_pre_mul4[0] = data_i[3] ^ data_i[1]; *)
    (* assign y_pre_mul4[1] = data_i[2] ^ data_i[0]; *)
    y_pre_mul4_0 <- xorv data_i[@3] data_i[@1] ;;
    y_pre_mul4_1 <- xorv data_i[@2] data_i[@0] ;;
    (* // Mul4(y_pre_mul4) *)
    (* for (genvar i = 0; i < 2; i++) begin : gen_mul4 *)
    (*   assign y[i] = aes_mul4(y_pre_mul4[i]); *)
    (* end *)
    y <- mapT aes_mul4 (y_pre_mul4_0 :: y_pre_mul4_1 :: []) ;;
    let y := unpeel y in

    (* // Drive y2_pre_mul2 *)
    (* assign y2_pre_mul2 = y[0] ^ y[1]; *)
    y2_pre_mul2 <- xorv y[@0] y[@1] ;;
    (* // Mul2(y) *)
    (* assign y2 = aes_mul2(y2_pre_mul2); *)
    y2 <- aes_mul2 y2_pre_mul2 ;;

    (* // Drive z *)
    (* assign z[0] = y2 ^ y[0]; *)
    (* assign z[1] = y2 ^ y[1]; *)
    z_0 <- xorv y2 y[@0] ;;
    z_1 <- xorv y2 y[@1] ;;
    let z := unpeel [z_0; z_1] in

    (* // Mux z *)
    (* assign z_muxed[0] = (op_i == CIPH_FWD) ? 8'b0 : z[0]; *)
    (* assign z_muxed[1] = (op_i == CIPH_FWD) ? 8'b0 : z[1]; *)
    z_muxed <- muxPair op_i (unpeel [zero_byte; zero_byte], z) ;;

    (* // Drive outputs *)
    (* assign data_o[0] = data_i[1] ^ x_mul2[3] ^ x[1] ^ z_muxed[1]; *)
    (* assign data_o[1] = data_i[0] ^ x_mul2[2] ^ x[1] ^ z_muxed[0]; *)
    (* assign data_o[2] = data_i[3] ^ x_mul2[1] ^ x[3] ^ z_muxed[1]; *)
    (* assign data_o[3] = data_i[2] ^ x_mul2[0] ^ x[3] ^ z_muxed[0]; *)
    data_o0 <- (xorv data_i[@1] x_mul2[@3] >>= xorv x[@1] >>= xorv z_muxed[@1]) ;;
    data_o1 <- (xorv data_i[@0] x_mul2[@2] >>= xorv x[@1] >>= xorv z_muxed[@0]) ;;
    data_o2 <- (xorv data_i[@3] x_mul2[@1] >>= xorv x[@3] >>= xorv z_muxed[@1]) ;;
    data_o3 <- (xorv data_i[@2] x_mul2[@0] >>= xorv x[@3] >>= xorv z_muxed[@0]) ;;

    ret (unpeel [data_o0; data_o1; data_o2; data_o3]).

  Definition aes_mix_columns
    (op_i : signal Bit) (a: signal (Vec (Vec (Vec Bit 8) 4) 4))
    : cava (signal (Vec (Vec (Vec Bit 8) 4) 4)) :=
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
    let transposed := aes_transpose a in
    mixed <- mapT (aes_mix_single_column op_i) (peel transposed) ;;
    ret (aes_transpose (unpeel mixed)).

End WithCava.

(* Interface designed to match interface of corresponding SystemVerilog component:
     https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_mix_columns.sv
*)
Definition aes_mix_columns_Interface :=
  combinationalInterface "aes_mix_columns"
  [mkPort "op_i" Bit; mkPort "data_i" (Vec (Vec (Vec Bit 8) 4) 4)]
  [mkPort "data_o" (Vec (Vec (Vec Bit 8) 4) 4)]
  [].

(* Create a netlist for the aes_mix_columns_Netlist block. The block is written with
   curried inputs but netlist extraction for top-level blocks requires they are
   written with a single argument, using tupling for composite inputs. A lambda
   expression maps from the tuple inputs to the curried arguments.  *)
Definition aes_mix_columns_Netlist
  := makeNetlist aes_mix_columns_Interface (fun '(op_i, data_i) => aes_mix_columns op_i data_i).

(* Test case from the first four rows of the Wikipedia page on AES mix_columns:
     https://en.wikipedia.org/wiki/Rijndael_MixColumns
*)
Definition mixColTest1InputNat : Vector.t (Vector.t nat 4) 4
  := [[219; 19; 83; 69];
      [242; 10; 34; 92];
      [1; 1; 1; 1];
      [45; 38; 49; 76]
  ].

Local Open Scope list_scope.

(* Get the test inputs into the right format for the circuit inputs. *)
Definition mix_cols_i1 := fromNatVec mixColTest1InputNat.
(* Compute the expected outputs from the Coq/Cava semantics. *)
Definition mix_cols_expected_outputs := combinational (aes_mix_columns [false] [mix_cols_i1]).

Definition aes_mix_columns_tb :=
  testBench "aes_mix_columns_tb"
            aes_mix_columns_Interface
            [(false, mix_cols_i1)]
            mix_cols_expected_outputs.
