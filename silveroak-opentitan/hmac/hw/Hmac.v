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

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.
Require Import Cava.TLUL.
Require Import Cava.Components.RealignMaskedFifo.

Require Import HmacHardware.Sha256.
Import ExprNotations.
Import PrimitiveNotations.

Local Open Scope N.

Section Var.
  Import ExprNotations.
  Context {var : tvar}.

  Definition hmac_register_count := 27%nat.
  Definition hmac_register_log_sz := 5%nat.

  Definition REG_INTR_STATE := Constant (BitVec hmac_register_log_sz) 0.
  Definition REG_CMD := Constant (BitVec hmac_register_log_sz) 5.
  Definition REG_INTR := Constant (BitVec hmac_register_log_sz) 0.
  Definition REG_DIGEST_0 := Constant (BitVec hmac_register_log_sz) 0x11.
  Definition REG_DIGEST_1 := Constant (BitVec hmac_register_log_sz) 0x12.
  Definition REG_DIGEST_2 := Constant (BitVec hmac_register_log_sz) 0x13.
  Definition REG_DIGEST_3 := Constant (BitVec hmac_register_log_sz) 0x14.
  Definition REG_DIGEST_4 := Constant (BitVec hmac_register_log_sz) 0x15.
  Definition REG_DIGEST_5 := Constant (BitVec hmac_register_log_sz) 0x16.
  Definition REG_DIGEST_6 := Constant (BitVec hmac_register_log_sz) 0x17.
  Definition REG_DIGEST_7 := Constant (BitVec hmac_register_log_sz) 0x18.
  Definition REG_KEY_0 := Constant (BitVec hmac_register_log_sz) 0x9.
  Definition REG_KEY_1 := Constant (BitVec hmac_register_log_sz) 0xA.
  Definition REG_KEY_2 := Constant (BitVec hmac_register_log_sz) 0xB.
  Definition REG_KEY_3 := Constant (BitVec hmac_register_log_sz) 0xC.
  Definition REG_KEY_4 := Constant (BitVec hmac_register_log_sz) 0xD.
  Definition REG_KEY_5 := Constant (BitVec hmac_register_log_sz) 0xE.
  Definition REG_KEY_6 := Constant (BitVec hmac_register_log_sz) 0xF.
  Definition REG_KEY_7 := Constant (BitVec hmac_register_log_sz) 0x10.

  (* Hmac_inner uses realigned fifo values and regsiter map *)
  (* state value = *)
  (* 1. Hash key ^ ipad *)
  (* 2. Hash message *)
  (* 3. Store digest and reset sha256 *)
  (* 4. Hash key ^ opad *)
  (* 5. Hash stored digest *)
  (* 6. Store digest and reset sha256 *)
  Definition hmac_inner : Circuit _
    [Vec (BitVec 32) hmac_register_count; Bit; BitVec 32; BitVec 4; Bit]
    (Vec (BitVec 32) hmac_register_count ** Bit) := {{
    fun registers fifo_valid fifo_data fifo_length fifo_final =>

    let/delay '(updated_registers, waiting_for_digest, accept_fifo, ptr, state, digest; sha_ready) :=

      let cmd_hash_start   := (`index` registers `REG_CMD` & `K 0x1`) == `K 0x1` in
      let cmd_hash_process := (`index` registers `REG_CMD` & `K 0x2`) == `K 0x2` in

      let state' : BitVec 5 :=
             if sha_ready && state == `K 1` && ptr == `K 15` then state + `K 1`
        (* cmd_hash_process is the end of message, but we also have to wait for
         * fifo to drain by observing fifo_valid *)
        else if sha_ready && state == `K 2` && cmd_hash_process && !fifo_valid  then state + `K 1`
        else if             state == `K 3`  && (!waiting_for_digest) then state + `K 1`
        else if sha_ready && state == `K 4` && ptr == `K 15` then state + `K 1`
        else if sha_ready && state == `K 5` && ptr == `K 7`  then state + `K 1`
        else if sha_ready && state == `K 6` && (!waiting_for_digest) then `K 0`
        else if state == `K 0` && cmd_hash_start then `K 1`
        else state in

      let ptr' : BitVec 6 :=
             if (state == `K 0`) || ! (state == state') then `K 0`
        else if !sha_ready then ptr
        else (ptr + `K 1`) in

      (* Keys start at byte address 0x24 or the 9th 32bit register *)
      let key_vec := `slice 9 8` registers in
      let key := `index` key_vec ptr in
      let digest_word := `index` digest ptr in

      let '(sha_stream_valid, sha_stream, sha_stream_final; sha_stream_final_length) :=
             if state == `K 1` then (`One`, key ^ `K 0x36363636`, `Zero`, `K 0`)
        else if state == `K 2` then (fifo_valid, fifo_data, fifo_final, fifo_length)
        (* else if state' == `K 3` *)
        else if state == `K 4` then (`One`, key ^ `K 0x5c5c5c5c`, `Zero`, `K 0`)
        else if state == `K 5` then (`One`, digest_word, (ptr == `K 7` ) , `K 4`)
        else (`Zero`, `K 0`, `Zero`, `K 0`)

      in

      (* I don't think we need to explicitly flush-
         if we are left in a bad state we might need to flush after the last state
      *)
      let sha_stream_flush := `Zero` in

      let '(sha_done, sha_digest; sha_ready)
        := `sha256` sha_stream_valid sha_stream sha_stream_final sha_stream_final_length sha_stream_flush in

      let is_consuming := state' == `K 2` && sha_ready in
      let next_digest := if sha_done then sha_digest else digest in

      (* update registers, alternatively this could moved outside hmac_inner *)
      let next_registers :=
        (* assert the INTR register `hmac_done` when we finish *)
        (fun regs => if (state == `K 6`) && (state' == `K 0`) then
          let regs := `replace` regs `REG_INTR` `K 1` in
          let regs := `replace` regs `REG_DIGEST_0` ( `index` sha_digest `Constant (BitVec 4) 0` ) in
          let regs := `replace` regs `REG_DIGEST_1` ( `index` sha_digest `Constant (BitVec 4) 1` ) in
          let regs := `replace` regs `REG_DIGEST_2` ( `index` sha_digest `Constant (BitVec 4) 2` ) in
          let regs := `replace` regs `REG_DIGEST_3` ( `index` sha_digest `Constant (BitVec 4) 3` ) in
          let regs := `replace` regs `REG_DIGEST_4` ( `index` sha_digest `Constant (BitVec 4) 4` ) in
          let regs := `replace` regs `REG_DIGEST_5` ( `index` sha_digest `Constant (BitVec 4) 5` ) in
          let regs := `replace` regs `REG_DIGEST_6` ( `index` sha_digest `Constant (BitVec 4) 6` ) in
          let regs := `replace` regs `REG_DIGEST_7` ( `index` sha_digest `Constant (BitVec 4) 7` ) in
          regs
        else regs)
        (* deassert the CMD registers once we no longer need them @ state > 3 *)
        (if state == `K 3` then `replace` registers `REG_CMD` `K 0` else registers)
      in

      let waiting_for_digest :=
        if (state' == `K 3`) || (state' == `K 6`)
        then ! sha_done
        else `Zero` in

      (next_registers, waiting_for_digest, is_consuming, ptr', state', next_digest, sha_ready)

      initially default
    in

    (updated_registers, accept_fifo)

  }}.

  Definition hmac : Circuit _ [Bit; BitVec 32; BitVec 5; BitVec 4; Bit] (Vec (BitVec 32) hmac_register_count) := {{
    fun write_en write_data write_address write_mask is_fifo_write =>
    let/delay '(sha_ready ; registers) :=

      (* TODO(blaxill): mask RO register writes *)
      let next_registers :=
        if write_en && !is_fifo_write
        then `replace (n:=hmac_register_count)` registers write_address write_data
        else registers
      in

      let cmd_hash_process := (`index` registers `REG_CMD` & `K 0x2`) == `K 0x2` in

      let '(fifo_valid, fifo_data, fifo_data_length, fifo_is_last; fifo_full) :=
        `realign_masked_fifo 256` (write_en && is_fifo_write) write_data write_mask cmd_hash_process sha_ready in

      let '(registers'; sha_ready) :=
        `hmac_inner` next_registers fifo_valid fifo_data fifo_data_length fifo_is_last in

      (sha_ready, registers')
      initially default

    in (registers)
  }}.


  Definition hmac_top : Circuit _ [tl_h2d_t] tl_d2h_t := {{
    fun incoming_tlp =>

    let/delay '(tl_o; registers) :=

      let '(tl_o, read_en, write_en, address, write_data; write_mask)
        := `tlul_adapter_reg` incoming_tlp registers in

      let aligned_address := `bvslice 2 5` address in

      let is_fifo_write := address >= `Constant (BitVec _) 2048` in

      let registers' := `hmac` write_en write_data aligned_address write_mask is_fifo_write in

      (tl_o, registers')

      initially default
    in tl_o
  }}.

End Var.

Section SanityCheck.
  Require Import Cava.Semantics.
  Require Import Coq.Lists.List.
  Import ListNotations.
  Open Scope list_scope.
  Close Scope circuit_type_scope.

  Definition pp {n} (v: denote_type (Vec (BitVec 32) n)) :=
    List.map HexString.of_N v.

  Definition is_done (v : denote_type (Vec (BitVec 32) hmac_register_count)) :=
    nth 0 (v) 0.

  Definition get_regs (v: denote_type (state_of hmac))
    : denote_type (Vec (BitVec 32) hmac_register_count) .
    cbv [state_of hmac absorb_any] in v.
    destruct v.
    destruct d as (_, regs).
    exact regs.
  Defined.

  (* We can set registers *)
  Goal
    let write_en := true in
    let write_data := 0xAAAAAAAAA in
    let write_address := 26 in
    let write_mask := 0xFFFFFFFF in
    let is_fifo_write := false in
    forall write_data,
    nth (N.to_nat write_address) (get_regs (
      fst (step hmac
         (reset_state hmac)
         (write_en, (write_data, (write_address, (write_mask, (is_fifo_write, tt)))))
      ))) 0
    = write_data.
  Proof. vm_compute; reflexivity. Qed.

  (* Set the key registers to the test key *)
  Definition state_with_key_registers_set :=
    Eval vm_compute in
    snd (simulate' hmac (
     List.map (fun v => (true, (snd v, (9 + fst v, (0xF, (false, tt))))))
      [ (0, 0x00010203)
      ; (1, 0x04050607)
      ; (2, 0x08090A0B)
      ; (3, 0x0C0D0E0F)
      ; (4, 0x10111213)
      ; (5, 0x14151617)
      ; (6, 0x18191A1B)
      ; (7, 0x1C1D1E1F)
      ]) (reset_state hmac)).

  (* digest registers get set to the correct digest *)
  Goal
    (* there are 8 digest registers start at 0x11*)
    firstn 8 (skipn 0x11
    (get_regs (snd (
    simulate' hmac
    (
     (* set cmd_start *)
     [ (true, (1, (5, (0xF, (false, tt))))) ] ++

     (* send message data to fifo *)
     (
     List.map (fun v => (true, (snd v, (512, (fst v, (true, tt))))))
      [
      ( 0xF, 0x53616D70 )
    ; ( 0xF, 0x6C65206D )
    ; ( 0xF, 0x65737361 )
    ; ( 0xF, 0x67652066 )
    ; ( 0xF, 0x6F72206B )
    ; ( 0xF, 0x65796C65 )
    ; ( 0xF, 0x6E3C626C )
    ; ( 0xF, 0x6F636B6C )
    ; ( 0xC, 0x656E0000 )

      ])

     (* signal cmd_processm  *)
      ++ [ (true, (3, (5, (0xF, (false, tt))))) ]

     (* wait for digest to be ready *)
     ++ repeat (false, (0, (0, (0, (false, tt))))) 350
      )
      state_with_key_registers_set))))
    = [0xA28CF431; 0x30EE696A; 0x98F14A37; 0x678B56BC; 0xFCBDD9E5; 0xCF69717F; 0xECF5480F; 0x0EBDF790].

  Proof. Time vm_compute; reflexivity. Qed.

End SanityCheck.
