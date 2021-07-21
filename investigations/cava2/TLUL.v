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

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.List.

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Semantics.

(* Naming and parameter choices follow OpenTitan conventions *)
Definition TL_AW  := 32.
Definition TL_DW  := 32.
Definition TL_AIW := 8.
Definition TL_DIW := 1.
Definition TL_DUW := 4.
Definition TL_DBW := 4. (* (TL_DW>>3). *)
Definition TL_SZW := 2. (* $clog2($clog2(TL_DBW)+1). *)

Notation BitVec n := (Vec Bit n).

(* (1* typedef struct packed { *1) *)
(* (1*   logic                         a_valid; *1)   1 *)
(* (1*   tl_a_op_e                     a_opcode; *1)  3 *)
(* (1*   logic                  [2:0]  a_param; *1)   3 *)
(* (1*   logic  [top_pkg::TL_SZW-1:0]  a_size; *1)    2 *)
(* (1*   logic  [top_pkg::TL_AIW-1:0]  a_source; *1)  8 *)
(* (1*   logic   [top_pkg::TL_AW-1:0]  a_address; *1) 32 *)
(* (1*   logic  [top_pkg::TL_DBW-1:0]  a_mask; *1)    4 *)
(* (1*   logic   [top_pkg::TL_DW-1:0]  a_data; *1)    32 *)
(* (1*   tl_a_user_t                   a_user; *1)    16 *)
(* (1*   logic                         d_ready; *1)   1 *)
(* (1* } tl_h2d_t; *1)
=102 *)
Definition tl_h2d_t :=
  Bit **
  BitVec 3 **
  BitVec 3 **
  BitVec TL_SZW **
  BitVec TL_AIW **
  BitVec TL_AW **
  BitVec TL_DBW **
  BitVec TL_DW **
  BitVec 16 **
  Bit.

(* typedef struct packed { *)
(*   logic                         d_valid; *)
(*   tl_d_op_e                     d_opcode; *)
(*   logic                  [2:0]  d_param; *)
(*   logic  [top_pkg::TL_SZW-1:0]  d_size; *)
(*   logic  [top_pkg::TL_AIW-1:0]  d_source; *)
(*   logic  [top_pkg::TL_DIW-1:0]  d_sink; *)
(*   logic   [top_pkg::TL_DW-1:0]  d_data; *)
(*   logic  [top_pkg::TL_DUW-1:0]  d_user; *)
(*   logic                         d_error; *)
(*   logic                         a_ready; *)
(* } tl_d2h_t; *)

Definition tl_d2h_t :=
  Bit **
  BitVec 3 **
  BitVec 3 **
  BitVec 2 **
  BitVec 8 **
  BitVec 1 **
  BitVec 32 **
  BitVec 4 **
  Bit **
  Bit.

(* typedef enum logic [2:0] { *)
(*   PutFullData    = 3'h 0, *)
(*   PutPartialData = 3'h 1, *)
(*   Get            = 3'h 4 *)
(* } tl_a_op_e; *)
Definition tl_a_op_e := Vec Bit 3.
Definition PutFullData := 0.
Definition PutPartialData := 1.
Definition Get := 4.

(* typedef enum logic [2:0] { *)
(*   AccessAck     = 3'h 0, *)
(*   AccessAckData = 3'h 1 *)
(* } tl_d_op_e; *)
Definition tl_d_op_e := Vec Bit 3.
Definition AccessAck := 0.
Definition AccessAckData := 1.

Section Var.
  Context {var : tvar}.

  Definition tlul_to_hw : Circuit _ [tl_h2d_t] [] := {{
    fun incoming_tlp =>

    let
      (a_valid
      , a_opcode
      , a_param
      , a_size
      , a_source
      , a_address
      , a_mask
      , a_data
      , a_user
      ; d_ready) := incoming_tlp in

    (* let/delay state := _ *)
    (*   initially _ in *)
       (* let curr_outstanding := read0(outstanding) in *)

       (* let a_ack := get(tl_i, a_valid) && !curr_outstanding in *)
       (* let d_ack := curr_outstanding && get(tl_i, d_ready) in *)

       (* let rd_req := a_ack && (get(tl_i, a_opcode) == enum TLUL.tl_a_op_e { Get } ) in *)
       (* let wr_req := a_ack && ( *)
       (*   get(tl_i, a_opcode) == enum TLUL.tl_a_op_e { PutFullData } || *)
       (*   get(tl_i, a_opcode) == enum TLUL.tl_a_op_e { PutPartialData } *)
       (* ) in *)

       (* (1* TODO(blaxill): skipping malformed tl packet detection *1) *)
       (* let err_internal := Ob~0 in *)
       (* let error_i := Ob~0 in *)

       (* if a_ack then ( *)
       (*   write0(reqid, get(tl_i, a_source)); *)
       (*   write0(reqsz, get(tl_i, a_size)); *)
       (*   write0(rspop, *)
       (*     if rd_req then enum TLUL.tl_d_op_e { AccessAckData } *)
       (*     else enum TLUL.tl_d_op_e { AccessAck }); *)
       (*   write0(error, error_i || err_internal); *)

       (*   write0(outstanding, Ob~1) *)
       (* ) *)
       (* else if d_ack then write0(outstanding, Ob~0) *)
       (* else pass; *)

       (* let we_o := wr_req && !err_internal in *)
       (* let re_o := rd_req && !err_internal in *)

       (* let wdata_o := get(tl_i, a_data) in *)
       (* let be_o    := get(tl_i, a_mask) in *)
       (* let reg_idx := get(tl_i, a_address)[|5`d2| :+ 5] in *)

       (* if we_o then ( *)
       (*   regs.(register_values.write)(reg_idx, wdata_o); *)
       (*   write_dirty.(register_bool_flag.write)(reg_idx, Ob~1) *)
       (* ) else pass; *)

       (* if re_o then ( *)
       (*   let val := regs.(register_values.read)(reg_idx) in *)
       (*   read_dirty.(register_bool_flag.write)(reg_idx, Ob~1); *)
       (*   write0(rdata, val) *)
       (* ) else pass *)
    `Constant (tt : denote_type Unit)`
  }}.

End Var.

