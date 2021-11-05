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
  Definition REG_CFG := Constant (BitVec hmac_register_log_sz) 4.
  Definition REG_CMD := Constant (BitVec hmac_register_log_sz) 5.
  Definition REG_STATUS := Constant (BitVec hmac_register_log_sz) 6.
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
    [Bit; BitVec 32; BitVec 4; Bit; Bit; Bit; Bit; Vec (BitVec 32) 8]
    (Bit ** Bit ** sha_digest) := {{
    fun fifo_valid fifo_data fifo_length fifo_final
      cmd_hash_start cmd_hash_process cmd_hmac_enable hmac_key_vec =>

    let/delay '(finishing, waiting_for_digest, accept_fifo, ptr, state, digest; sha_ready) :=

      let state' : BitVec 5 :=
        if cmd_hmac_enable then
               if sha_ready && state == `K 1` && ptr == `K 15` then `K 2`
          (* cmd_hash_process is the end of message, but we also have to wait for
           * fifo to drain by observing fifo_final *)
          else if sha_ready && state == `K 2` && cmd_hash_process && fifo_final  then `K 3`
          else if              state == `K 3`  && (!waiting_for_digest) then `K 4`
          else if sha_ready && state == `K 4` && ptr == `K 15` then `K 5`
          else if sha_ready && state == `K 5` && ptr == `K 7`  then `K 6`
          else if sha_ready && state == `K 6` && (!waiting_for_digest) then `K 0`
          else if state == `K 0` && cmd_hash_start then `K 1`
          else state
        else
          (* in hmac bypass == sha only mode, we skip the key prefix step *)
               if state == `K 0` && cmd_hash_start then `K 2`
          else if sha_ready && state == `K 2` && cmd_hash_process && fifo_final then `K 3`
          else if state == `K 3` && (!waiting_for_digest) then `K 0`
          else state
      in

      let ptr' : BitVec 6 :=
             if (state == `K 0`) || ! (state == state') then `K 0`
        else if !sha_ready then ptr
        else (ptr + `K 1`) in

      (* Keys start at byte address 0x24 or the 9th 32bit register *)
      let key := `index` hmac_key_vec ptr in
      let digest_word := `index` digest ptr in

      let '(sha_stream_valid, sha_stream, sha_stream_final; sha_stream_final_length) :=
             if state == `K 1` then (`One`, key ^ `K 0x36363636`, `Zero`, `K 0`)
        else if state == `K 2` then (fifo_valid, fifo_data, fifo_final, fifo_length)
        (* else if state' == `K 3` *)
        else if state == `K 4` then (`One`, key ^ `K 0x5c5c5c5c`, `Zero`, `K 0`)
        else if state == `K 5` then (`One`, digest_word, (ptr == `K 7` ) , `K 4`)
        else (`Zero`, `K 0`, `Zero`, `K 0`)

      in

      let sha_stream_flush := if state == `K 0` then `One` else `Zero` in

      (* Our proof precondition for sha256 needs us to mask when it is not ready *)
      let sha_stream_valid' := if sha_ready then sha_stream_valid else `Zero` in

      let '(sha_done, sha_digest; sha_ready)
        := `sha256` sha_stream_valid' sha_stream sha_stream_final sha_stream_final_length sha_stream_flush in

      let is_consuming := state == `K 2` && sha_ready in
      let next_digest := if sha_done then sha_digest else digest in
      let state_is_zero := state == `K 0` in
      let is_finishing := ! state_is_zero && state' == `K 0` in

      let waiting_for_digest :=
        if (state' == `K 3`) || (state' == `K 6`)
        then ! sha_done
        else `Zero` in

      (is_finishing, waiting_for_digest, is_consuming, ptr', state', next_digest, sha_ready)

      initially default
    in

    (accept_fifo, finishing, digest)

  }}.

  Definition hmac : Circuit _ [Bit; BitVec 32; BitVec 5; BitVec 4; Bit; (Vec (BitVec 32) hmac_register_count)] (Vec (BitVec 32) hmac_register_count) := {{
    fun write_en write_data write_address write_mask is_fifo_write registers =>
    let/delay '(sha_ready ; out_registers) :=

      let cmd_hash_start   := (`index` registers `REG_CMD` & `K 0x1`) == `K 0x1` in
      let cmd_hash_process := (`index` registers `REG_CMD` & `K 0x2`) == `K 0x2` in
      let cmd_hmac_enable  := (`index` registers `REG_CFG` & `K 0x1`) == `K 0x1` in

      (* Keys start at byte address 0x24 or the 9th 32bit register *)
      let hmac_key := `slice 9 8` registers in

      let '(fifo_valid, fifo_data, fifo_data_length, fifo_is_last; fifo_full) :=
        `realign_masked_fifo 256` is_fifo_write write_data write_mask cmd_hash_process sha_ready in

      (* BUG:
         - the realigned fifo core currently doesn't signal last if the fifo is
          drained before flushing, and the number of bytes written mod 4 = 0
         - it probably should signal fifo_is_last once even if drained
         - but definitely should if it drains after flush is signaled
         - the easiest fix in that circuit would result is last being signaled a cycle later
           with a length of 0
         - however, the SHA256 core & spec requires the last word length to be > 0 so instead
         buffer the fifo data here and detect if it is the last word. *)
      let/delay
        '(buff_fifo_valid, buff_fifo_data, buff_fifo_data_length, buff_fifo_is_last
         , out_fifo_valid, out_fifo_data, out_fifo_data_length; out_fifo_is_last) :=

        if sha_ready then

          if cmd_hash_process && ! fifo_valid && ! buff_fifo_is_last then
            (* We have not yet signaled last *)
            ( `Zero`, `K 0`, `K 0`, `Zero`
            , `One`, buff_fifo_data, `K 4`, `One`)
          else
            if fifo_valid || cmd_hash_process then
              ( fifo_valid, fifo_data, fifo_data_length, fifo_is_last
              , buff_fifo_valid, buff_fifo_data, buff_fifo_data_length, buff_fifo_is_last )
            else
              ( buff_fifo_valid, buff_fifo_data, buff_fifo_data_length, buff_fifo_is_last
              , `Zero`, `K 0`, `K 0`, `Zero`)
         (* Sha not ready, nothing moves *)
        else
          ( buff_fifo_valid, buff_fifo_data, buff_fifo_data_length, buff_fifo_is_last
          , out_fifo_valid, out_fifo_data, out_fifo_data_length, out_fifo_is_last)

        initially default
      in


      let '(sha_ready, hmac_done; digest) :=
        (* `hmac_inner` fifo_valid fifo_data fifo_data_length fifo_is_last *)
        `hmac_inner` out_fifo_valid out_fifo_data out_fifo_data_length out_fifo_is_last
        cmd_hash_start cmd_hash_process cmd_hmac_enable
        hmac_key
      in

      let set_done :=
        (* deassert the CMD registers if we are finishing *)
        if hmac_done then `replace` registers `REG_CMD` `K 0` else registers
      in

      let set_fifo_full :=
        (* set the fifo_full STATUS register *)
        (* hmac.STATUS @ 0x18 *)
        (* bit: 0:fifo_empty, 1:fifo_full, 8:4: fifo_depth *)
        `replace` set_done `REG_STATUS` (if fifo_full then `K 2` else `K 0`)
      in

      let next_registers :=
        (* assert the INTR register `hmac_done` when we finish *)
        (fun regs => if hmac_done then
          let regs := `replace` regs `REG_INTR_STATE` `K 1` in
          let regs := `replace` regs `REG_DIGEST_0` ( `index` digest `Constant (BitVec 4) 0` ) in
          let regs := `replace` regs `REG_DIGEST_1` ( `index` digest `Constant (BitVec 4) 1` ) in
          let regs := `replace` regs `REG_DIGEST_2` ( `index` digest `Constant (BitVec 4) 2` ) in
          let regs := `replace` regs `REG_DIGEST_3` ( `index` digest `Constant (BitVec 4) 3` ) in
          let regs := `replace` regs `REG_DIGEST_4` ( `index` digest `Constant (BitVec 4) 4` ) in
          let regs := `replace` regs `REG_DIGEST_5` ( `index` digest `Constant (BitVec 4) 5` ) in
          let regs := `replace` regs `REG_DIGEST_6` ( `index` digest `Constant (BitVec 4) 6` ) in
          let regs := `replace` regs `REG_DIGEST_7` ( `index` digest `Constant (BitVec 4) 7` ) in
          regs
        else regs) set_fifo_full
      in


      (sha_ready, next_registers)
      initially default

    in (out_registers)
  }}.

  Definition mask_valid : Circuit [] [tl_h2d_t; Bit] tl_h2d_t := {{
    fun incoming_tlp clear_valid =>
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

    (if clear_valid then `Zero` else a_valid
    , a_opcode
    , a_param
    , a_size
    , a_source
    , a_address
    , a_mask
    , a_data
    , a_user
    , d_ready)
  }}.

  Definition mask_ready : Circuit [] [tl_d2h_t; Bit] tl_d2h_t := {{
    fun outgoing_tlp clear_ready =>
    let
      '(d_valid
      , d_opcode
      , d_param
      , d_size
      , d_source
      , d_sink
      , d_data
      , d_user
      , d_error
      ; a_ready
      ) := outgoing_tlp in

    ( d_valid
    , d_opcode
    , d_param
    , d_size
    , d_source
    , d_sink
    , d_data
    , d_user
    , d_error
    , if clear_ready then `Zero` else a_ready
    )
  }}.

  Definition hmac_top : Circuit _ [tl_h2d_t] tl_d2h_t := {{
    fun incoming_tlp =>

    let/delay '(was_fifo_full, tl_o; registers) :=

      let is_fifo_full :=
        (`index` registers `REG_STATUS` & `K 0x2` ) == `K 0x2`
      in

      (* Mask incoming tlp validity, outgoing tlp ready if we are full. *)
      let incoming_tlp' := `mask_valid` incoming_tlp is_fifo_full in

      let '(tl_o, read_en, write_en, address, write_data; write_mask)
        := `tlul_adapter_reg` incoming_tlp' registers in

      let aligned_address := `bvslice 2 5` address in
      let is_fifo_write := address >= `Constant (BitVec _) 2048` in

      let next_registers :=
        if write_en && !is_fifo_write
        then (
          (* all writes to REG_INTR_STATE are w1c *)
          if aligned_address == `REG_INTR_STATE`
          then
            let val := `index` registers `REG_INTR_STATE` in
            let cleared_val := val & ( ~  write_data ) in
            `replace (n:=hmac_register_count)` registers `REG_INTR_STATE` cleared_val
          else
          (`replace (n:=hmac_register_count)` registers aligned_address write_data))
        else registers
      in

      let write_en' :=
        write_en && !is_fifo_write && !(aligned_address == `REG_INTR_STATE`)
      in

      (* We cant be setting a register and writing to the fifo so we can use
         'registers' vs 'next_registers' *)
      let cmd_cfg_endian_swap  := (`index` registers `REG_CFG` & `K 0x4`) == `K 0x4` in
      let write_data' :=
        if (is_fifo_write && cmd_cfg_endian_swap)
        then `endian_swap32` write_data
        else write_data
      in

      let registers' := `hmac` write_en' write_data' aligned_address write_mask is_fifo_write next_registers in

      (is_fifo_full, tl_o, registers')

      initially default
    in `mask_ready` tl_o was_fifo_full
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

  Definition get_regs (v: denote_type (state_of hmac_top))
    : denote_type (Vec (BitVec 32) hmac_register_count) .
    cbv [state_of hmac absorb_any] in v.
    destruct v.
    destruct d as (_, (_, regs)).
    exact regs.
  Defined.

  Definition to_write_tlp addr mask val : denote_type [tl_h2d_t] :=
    (true, (PutFullData, (0, (2, (0, (addr, (mask, (val, (0, true)))))))), tt).
  Definition to_read_tlp addr : denote_type [tl_h2d_t] :=
    (true, (Get, (0, (2, (0, (addr, (0xF, (0, (0, true)))))))), tt).
  Definition empty_tlp : denote_type [tl_h2d_t] :=
    (false, (PutFullData, (0, (2, (0, (0, (0, (0, (0, true)))))))), tt).

  (* TODO: write proper test bench e.g. hw/Sha256Tests.v *)
  (* Set the key registers to the test key *)
  Definition state_with_key_registers_set :=
    Eval vm_compute in
    snd ((simulate' hmac_top (
    [ to_write_tlp 0x24 0xF 0x00010203
    ; empty_tlp
    ; to_write_tlp 0x28 0xF 0x04050607
    ; empty_tlp
    ; to_write_tlp 0x2C 0xF 0x08090A0B
    ; empty_tlp
    ; to_write_tlp 0x30 0xF 0x0C0D0E0F
    ; empty_tlp
    ; to_write_tlp 0x34 0xF 0x10111213
    ; empty_tlp
    ; to_write_tlp 0x38 0xF 0x14151617
    ; empty_tlp
    ; to_write_tlp 0x3C 0xF 0x18191A1B
    ; empty_tlp
    ; to_write_tlp 0x40 0xF 0x1C1D1E1F
    ; empty_tlp
    ]) (reset_state hmac_top))).

  Fixpoint repeat2 {A} x y n : list A :=
    match n with
    | O => [x;y]
    | S n' => x :: y :: repeat2 x y n'
    end.

  (* digest registers get set to the correct digest *)
  Goal
  (* exists x, *)
    (* there are 8 digest registers start at 0x11*)
    firstn 8 (skipn 0x11
    (get_regs (
    snd (
    simulate' hmac_top
    (
     (* set hmac_en *)
    [ to_write_tlp 16 0x1 1 ; empty_tlp] ++
     (* set cmd_start *)
     [ to_write_tlp 20 0x1 1; empty_tlp ] ++

      [ to_write_tlp 2048 0xF 0x53616D70 ; empty_tlp
      ; to_write_tlp 2048 0xF 0x6C65206D ; empty_tlp
      ; to_write_tlp 2048 0xF 0x65737361 ; empty_tlp
      ; to_write_tlp 2048 0xF 0x67652066 ; empty_tlp
      ; to_write_tlp 2048 0xF 0x6F72206B ; empty_tlp
      ; to_write_tlp 2048 0xF 0x65796C65 ; empty_tlp
      ; to_write_tlp 2048 0xF 0x6E3C626C ; empty_tlp
      ; to_write_tlp 2048 0xF 0x6F636B6C ; empty_tlp
      ; to_write_tlp 2048 0xC 0x656E0000 ; empty_tlp
      ]

     (* (1* signal cmd_processm  *1) *)
      ++ [ to_write_tlp 20 0xF 3; empty_tlp ]

     (* (1* wait for digest to be ready *1) *)
     ++ repeat empty_tlp 350
      )
      state_with_key_registers_set))))
    =
    [0xA28CF431; 0x30EE696A; 0x98F14A37; 0x678B56BC; 0xFCBDD9E5; 0xCF69717F; 0xECF5480F; 0x0EBDF790].

  Proof. Time vm_compute; reflexivity. Qed.

  (* SHA256 "abc" in SHA only mode is correct *)
  Goal
    firstn 8 (skipn 0x11
    (get_regs (
    snd (
    simulate' hmac_top
    (

     (*  hmac_en *)
     [ to_write_tlp 16 0x1 0 ; empty_tlp] ++
     (* set cmd_start *)
     [ to_write_tlp 20 0x1 1; empty_tlp ] ++

      [ to_write_tlp 2048 0xE 0x61626364 ; empty_tlp
      ]

      ++ [ to_write_tlp 20 0xF 3; empty_tlp ]

     (* (1* wait for digest to be ready *1) *)
     ++ repeat empty_tlp 82
      )
      (reset_state hmac_top))
      )))
    =
      [ 0xBA7816BF
      ; 0x8F01CFEA
      ; 0x414140DE
      ; 0x5DAE2223
      ; 0xB00361A3
      ; 0x96177A9C
      ; 0xB410FF61
      ; 0xF20015AD
      ].
  Proof. Time vm_compute; reflexivity. Qed.

  Goal
    firstn 8 (skipn 0x11
    (get_regs (
    snd (
    simulate' hmac_top
    (

     (*  hmac_en *)
     [ to_write_tlp 16 0x1 0 ; empty_tlp] ++
     (* set cmd_start *)
     [ to_write_tlp 20 0x1 1; empty_tlp ] ++

      [ to_write_tlp 2048 0xf 0x61626364 ; empty_tlp
      ]

      ++ [ to_write_tlp 20 0xF 3; empty_tlp ]

     (* (1* wait for digest to be ready *1) *)
     ++ repeat empty_tlp 82
      )
      (reset_state hmac_top))
      )))
    =
      [ 0x88d4266f
      ; 0xd4e6338d
      ; 0x13b845fc
      ; 0xf289579d
      ; 0x209c8978
      ; 0x23b9217d
      ; 0xa3e16193
      ; 0x6f031589
      ].
  Proof. Time vm_compute; reflexivity. Qed.


End SanityCheck.

