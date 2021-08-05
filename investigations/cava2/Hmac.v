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
Require Import Cava.Primitives.
Require Import Cava.Sha256.
Require Import Cava.TLUL.

Import ExprNotations.
Import PrimitiveNotations.

Local Open Scope N.

Section Var.
  Import ExprNotations.
  Context {var : tvar}.

  Definition hmac_register_count := 27%nat.
  Definition hmac_register_index := 5%nat.
  Definition hmac_register := BitVec hmac_register_index.

  Definition REG_INTR_STATE := Constant (0: denote_type hmac_register).
  Definition REG_CMD := Constant (5: denote_type hmac_register).

  Definition hmac_top : Circuit _ [tl_h2d_t] tl_d2h_t := {{
    fun incoming_tlp =>

    let/delay '(tl_o; registers) :=

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
      let cmd_start := write_en && aligned_address == `REG_CMD` && write_data == `K 1` && !fifo_write in
      (* cmd_process is set when host writes to hmac.CMD.hash_process *)
      (* and signifies the end of a message *)
      let cmd_process := write_en && aligned_address == `REG_CMD` && write_data == `K 2` && !fifo_write in

      let '(packer_valid; packer_data)
        := `tlul_pack` (write_en && fifo_write) write_data write_mask cmd_process in

      (* TODO(blaxill): FIX ME *)
      (* let '(_, padded_block; padded_valid) := `sha256_padder` packer_valid packer_data cmd_process `circuit_hole` cmd_start in *)
      (* TODO(blaxill): sha needs to block FIFO writes and process HMAC key first *)
      (* let inital_digest := `Constant sha256_initial_digest` in *)
      (* let '(digest; digest_valid) := `sha256_inner` padded_block padded_valid `circuit_hole` in *)
      (* let next_digest := if digest_valid then digest else digest_buffer in *)

      (tl_o, nregisters)

      initially value_hole
    in tl_o
  }}.

End Var.

