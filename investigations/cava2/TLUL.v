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

Section Var.
  Import ExprNotations.
  Context {var : tvar}.

  Definition False := Constant (false: denote_type Bit).
  Definition _0 {sz} := Constant (0: denote_type (BitVec sz)).
  Definition _1 {sz} := Constant (1: denote_type (BitVec sz)).
  Definition _2 {sz} := Constant (2: denote_type (BitVec sz)).

  (* typedef enum logic [2:0] { *)
  (*   PutFullData    = 3'h 0, *)
  (*   PutPartialData = 3'h 1, *)
  (*   Get            = 3'h 4 *)
  (* } tl_a_op_e; *)
  Definition tl_a_op_e      := Vec Bit 3.
  Definition PutFullData    := Constant (0: denote_type tl_a_op_e).
  Definition PutPartialData := Constant (1: denote_type tl_a_op_e).
  Definition Get            := Constant (4: denote_type tl_a_op_e).

  (* typedef enum logic [2:0] { *)
  (*   AccessAck     = 3'h 0, *)
  (*   AccessAckData = 3'h 1 *)
  (* } tl_d_op_e; *)
  Definition tl_d_op_e     := Vec Bit 3.
  Definition AccessAck     := Constant (0: denote_type tl_d_op_e).
  Definition AccessAckData := Constant (1: denote_type tl_d_op_e).

  Definition io_req :=
    Bit **          (* write *)
    BitVec TL_AW ** (* address *)
    BitVec TL_DW ** (* write_data *)
    BitVec TL_DBW   (* write_mask *)
    .

  Definition sha_word := BitVec 32.
  Definition sha_block := Vec sha_word 16.
  Definition sha_digest := Vec sha_word 8.

  Axiom prim_and :
    forall {s1 s2},
    Circuit s1 [] Bit ->
    Circuit s2 [] Bit ->
    Circuit (s1++s2) [] Bit.
  Notation "x && y" := (prim_and x y) (in custom expr at level 20, left associativity) : expr_scope.

  Axiom prim_or :
    forall {s1 s2},
    Circuit s1 [] Bit ->
    Circuit s2 [] Bit ->
    Circuit (s1++s2) [] Bit.
  Notation "x || y" := (prim_or x y) (in custom expr at level 20, left associativity) : expr_scope.

  Axiom prim_not :
    forall {s1 },
    Circuit s1 [] Bit ->
    Circuit s1 [] Bit.
  Notation "! x" := (prim_not x) (in custom expr at level 20) : expr_scope.

  Axiom prim_gte :
    forall {s1 s2 t},
    Circuit s1 [] t ->
    Circuit s2 [] t ->
    Circuit (s1++s2) [] Bit.
  Notation "x >= y" := (prim_gte x y) (in custom expr at level 19, no associativity) : expr_scope.

  Axiom prim_eq :
    forall {s1 s2 t},
    Circuit s1 [] t ->
    Circuit s2 [] t ->
    Circuit (s1++s2) [] Bit.
  Notation "x == y" := (prim_eq x y) (in custom expr at level 19, no associativity) : expr_scope.

  Axiom slice :
    forall {t n} (start len: nat), Circuit [] [Vec t n] (Vec t len).

  Axiom index :
    forall {t n i}, Circuit [] [Vec t n; BitVec i] t.
  Axiom replace :
    forall {t n i}, Circuit [] [Vec t n; BitVec i; t] (Vec t n).

  Axiom value_hole : forall {t}, t.
  Axiom circuit_hole : forall {t}, Circuit [] [] t.

  (* Convert TLUL packets to a simple read/write register interface *)
  (* This is similar to OpenTitan's tlul_adapter_reg, but for simplicity we
   * provide all registers for the adapter to read from, rather than providing
   * a readback signal. Providing a same-cycle readback signal like OT version
   * is difficult without delayless loop *)
  Definition tlul_adapter_reg {reg_count}
    : Circuit _ [tl_h2d_t; Vec (BitVec 32) reg_count ] (tl_d2h_t ** io_req) := {{
    fun incoming_tlp registers =>
    let
      '(a_valid
      , a_opcode
      , a_param
      , a_size
      , a_source
      , a_address
      , a_mask
      , a_data
      , a_user
      ; d_ready) := incoming_tlp in

    let/delay '(reqid, reqsz, rspop, error, outstanding, we_o; re_o) :=

      let a_ack := a_valid && !outstanding in
      let d_ack := outstanding && d_ready in

      let rd_req := a_ack && a_opcode == `Get` in
      let wr_req := a_ack &&
        (a_opcode == `PutFullData` || a_opcode == `PutPartialData`) in

      (* TODO(blaxill): skipping malformed tl packet detection *)
      let err_internal := `False` in
      let error_i := `False` in

      let '(reqid, reqsz, rspop, error; outstanding) :=
        if a_ack then
          ( a_source
          , a_size
          , if rd_req then `AccessAckData` else `AccessAck`
          , error_i || err_internal
          , `False`
          )
        else
          (reqid, reqsz, rspop, error, if d_ack then `False` else outstanding)
      in

      let we_o := wr_req && !err_internal in
      let re_o := rd_req && !err_internal in

      (reqid, reqsz, rspop, error, outstanding, we_o, re_o)
      initially (0,(0,(0,(false,(false,(false,false))))))
        : denote_type (BitVec _ ** BitVec _ ** BitVec _ ** Bit ** Bit ** Bit ** Bit)
    in

    let wdata_o := a_data in
    let be_o    := a_mask in

    ( ( outstanding
      , rspop
      , `_0`
      , reqsz
      , reqid
      , `_0`
      , `index` registers (`slice 2 30` a_address)
      , `_0`
      , error
      , !outstanding
      )
    , (we_o, a_address, a_data, a_mask)
    )

  }}.

  (* Pack partial TLUL writes back into 32 bit blocks *)
  Definition tlul_pack : Circuit _ [Bit; BitVec 32; BitVec 4; Bit] (Bit ** BitVec 32) := {{
    fun valid data mask flush =>
    (* TODO(blaxill): *)
    (valid, data)
  }}.

  (* SHA-256 message padding *)
  Definition sha256_padder : Circuit _ [Bit; sha_word; Bit; Bit] (sha_block ** Bit) := {{
    (* TODO(blaxill): *)
    fun valid data finish clear => (`circuit_hole`, `False`)
  }}.

  (* TODO(blaxill): *)
  Definition sha256_initial_digest : Circuit [] [] sha_digest := circuit_hole.
  (* TODO(blaxill): *)
  Definition sha256_round_constants : Circuit [] [] sha_digest := circuit_hole.
  (* TODO(blaxill): *)
  Definition sha256_compress : Circuit _ [sha_digest; sha_word; sha_word] sha_digest := {{
    fun _ _ _ => `circuit_hole`
  }}.

  (* SHA-256 core *)
  Definition sha256 : Circuit _ [sha_block; Bit; Bit] (sha_digest ** Bit) := {{
    (* TODO(blaxill): *)
    fun data valid reset_digest =>
    (`circuit_hole`, `circuit_hole`)
  }}.


  Definition hmac_register_count := 27.
  Definition hmac_register_index := 5.
  Definition hmac_register := BitVec hmac_register_index.

  Definition REG_INTR_STATE := Constant (0: denote_type hmac_register).
  Definition REG_CMD := Constant (5: denote_type hmac_register).

  Unset Printing Notations.

  Definition hmac_top : Circuit _ [tl_h2d_t] tl_d2h_t := {{
    fun incoming_tlp =>

    let/delay '(digest_buffer, tl_o; registers) :=

      let '(tl_o, write_en, write_address, write_data; write_mask)
        := `tlul_adapter_reg` incoming_tlp registers in
      let aligned_address := `slice 2 5` write_address in

      let fifo_write := write_address >= `Constant (2048: denote_type (BitVec _))` in

      (* TODO(blaxill): ignore/mask writes to CMD etc ? *)
      (* TODO(blaxill): apply mask to register writes*)
      let nregisters :=
        if write_en && !fifo_write
        then `replace (n:=hmac_register_count)` registers aligned_address write_data
        else registers
      in

      (* cmd_start is set when host writes to hmac.CMD.hash_start *)
      (* and signifies the start of a new message *)
      let cmd_start := write_en && aligned_address == `REG_CMD` && write_data == `_1` && !fifo_write in
      (* cmd_process is set when host writes to hmac.CMD.hash_process *)
      (* and signifies the end of a message *)
      let cmd_process := write_en && aligned_address == `REG_CMD` && write_data == `_2` && !fifo_write in

      let '(packer_valid; packer_data)
        := `tlul_pack` (write_en && fifo_write) write_data write_mask cmd_process in

      let '(padded_block; padded_valid) := `sha256_padder` packer_valid packer_data cmd_process cmd_start in
      (* TODO(blaxill): sha needs to block FIFO writes and process HMAC key first *)
      let '(digest; digest_valid) := `sha256` padded_block padded_valid cmd_start in

      let next_digest := if digest_valid then digest else digest_buffer in

      (next_digest, tl_o, nregisters) initially value_hole

    in tl_o
  }}.

End Var.

