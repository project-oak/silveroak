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

Require Import Coq.Vectors.Vector.
Import VectorNotations.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Cava.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.Multiplexers.
Require Import AcornAes.Pkg.

Local Notation byte := (Vec Bit 8) (only parsing).
Local Notation "v [@ n ]" := (indexConst v n) (at level 1, format "v [@ n ]").

Section WithCava.
  Context {signal} {semantics : Cava signal}.

  Definition aes_shift_rows
    (op_i: signal Bit)
    (data_i: signal (Vec (Vec byte 4) 4))
    : cava (signal (Vec (Vec byte 4) 4)) :=
  (* Get separate rows from the input data *)
  data_i_0 <- data_i[@0] ;;
  data_i_1 <- data_i[@1] ;;
  data_i_2 <- data_i[@2] ;;
  data_i_3 <- data_i[@3] ;;

  (* // Row 0 is left untouched *)
  (* assign data_o[0] = data_i[0]; *)
  let data_o_0 := data_i_0 in

  (* // Row 2 does not depend on op_i *)
  (* assign data_o[2] = aes_circ_byte_shift(data_i[2], 2'h2); *)
  data_o_2 <- aes_circ_byte_shift 2 data_i_2 ;;

  (* // Row 1 *)
  (* assign data_o[1] = (op_i == CIPH_FWD) ? aes_circ_byte_shift(data_i[1], 2'h3) *)
  (*                                       : aes_circ_byte_shift(data_i[1], 2'h1); *)
  data_o_1_0 <- aes_circ_byte_shift 3 data_i_1 ;;
  data_o_1_1 <- aes_circ_byte_shift 1 data_i_1 ;;
  data_o_1 <- mux2 op_i (data_o_1_0, data_o_1_1) ;;

  (* // Row 3 *)
  (* assign data_o[3] = (op_i == CIPH_FWD) ? aes_circ_byte_shift(data_i[3], 2'h1) *)
  (*                                       : aes_circ_byte_shift(data_i[3], 2'h3); *)
  data_o_3_0 <- aes_circ_byte_shift 1 data_i_3 ;;
  data_o_3_1 <- aes_circ_byte_shift 3 data_i_3 ;;
  data_o_3 <- mux2 op_i (data_o_3_0, data_o_3_1) ;;

  packV [data_o_0; data_o_1; data_o_2; data_o_3].

End WithCava.
