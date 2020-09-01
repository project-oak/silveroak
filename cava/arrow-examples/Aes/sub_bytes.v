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
  
(* module aes_sub_bytes #(
  parameter SBoxImpl = "lut"
) (
  input  aes_pkg::ciph_op_e    op_i,
  input  logic [3:0][3:0][7:0] data_i,
  output logic [3:0][3:0][7:0] data_o
); *)
Definition aes_sub_bytes
  (sbox_type: SboxImpl)
  :  
    <<Bit, Vector (Vector (Vector Bit 8) 4) 4, Unit>> ~> 
      Vector (Vector (Vector Bit 8) 4) 4 :=
  (* // Individually substitute bytes
  for (genvar j = 0; j < 4; j++) begin : gen_sbox_j
    for (genvar i = 0; i < 4; i++) begin : gen_sbox_i
      aes_sbox #(
        .SBoxImpl ( SBoxImpl )
      ) aes_sbox_ij (
        .op_i   ( op_i         ),
        .data_i ( data_i[i][j] ),
        .data_o ( data_o[i][j] )
      );
    end
  end *)
  let sbox := curry (aes_sbox sbox_type) in
  let mapped_sbox := <[ !(map sbox) ]> in
  <[ \op_i data_i => 
    (* duplicate op_i to the same shape of data_i and then zip *)
    let op_i' = !replicate (!replicate op_i) in
    let zipped = !(map2 zipper) op_i' data_i in
    !(map mapped_sbox) zipped ]>.