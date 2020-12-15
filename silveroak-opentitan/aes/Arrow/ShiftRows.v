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

Require Import Aes.Pkg.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.

(* module aes_shift_rows (
  input  aes_pkg::ciph_op_e    op_i,
  input  logic [3:0][3:0][7:0] data_i,
  output logic [3:0][3:0][7:0] data_o
); *)
Definition aes_shift_rows
  : <<Bit, Vector (Vector (Vector Bit 8) 4) 4, Unit>> ~> Vector (Vector (Vector Bit 8) 4) 4 :=
  <[\op_i data_i =>
  (* // Row 0 is left untouched *)
  (* assign data_o[0] = data_i[0]; *)
    let data_o_0 = data_i[#0] in
  (* // Row 2 does not depend on op_i *)
  (* assign data_o[2] = aes_circ_byte_shift(data_i[2], 2'h2); *)
    let data_o_2 = !aes_circ_byte_shift data_i[#2] (#2) in

  (* // Row 1 *)
  (* assign data_o[1] = (op_i == CIPH_FWD) ? aes_circ_byte_shift(data_i[1], 2'h3) *)
  (*                                       : aes_circ_byte_shift(data_i[1], 2'h1); *)
    let data_o_1 =
      if op_i == !CIPH_FWD
      then !aes_circ_byte_shift data_i[#1] #3
      else !aes_circ_byte_shift data_i[#1] #1
      in
  (* // Row 3 *)
  (* assign data_o[3] = (op_i == CIPH_FWD) ? aes_circ_byte_shift(data_i[3], 2'h1) *)
  (*                                       : aes_circ_byte_shift(data_i[3], 2'h3); *)
    let data_o_3 =
      if op_i == !CIPH_FWD
      then !aes_circ_byte_shift data_i[#3] #1
      else !aes_circ_byte_shift data_i[#3] #3
      in
    data_o_0 :: data_o_1 :: data_o_2 :: data_o_3 :: []
  ]>.

Definition shift_rows_composed
:  << Vector _ 4, Unit>> ~> (Vector _ 4) :=
  <[\input =>
  let encoded = !aes_shift_rows !CIPH_FWD input in
  let decoded = !aes_shift_rows !CIPH_INV encoded in
  decoded ]>.
