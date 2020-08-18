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

From ArrowExamples Require Import Combinators Aes.pkg Aes.sbox Aes.mix_single_column.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

(* module aes_mix_columns (
  input  aes_pkg::ciph_op_e    op_i,
  input  logic [3:0][3:0][7:0] data_i,
  output logic [3:0][3:0][7:0] data_o
); *)
Definition aes_mix_columns
  :  
    <<Bit, Vector (Vector (Vector Bit 8) 4) 4, Unit>> ~> 
      Vector (Vector (Vector Bit 8) 4) 4 :=
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
  <[\op_i data_i =>
    let transposed = !aes_transpose data_i in
    let ouput_transposed = !(map2 aes_mix_single_column) (!replicate op_i) transposed in
    !aes_transpose ouput_transposed
  ]>.