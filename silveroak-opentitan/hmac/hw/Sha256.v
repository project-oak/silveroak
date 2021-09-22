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

Require Import Coq.Strings.String.
Require Import Coq.Strings.HexString.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.

Import ListNotations.
Import PrimitiveNotations.

Local Open Scope string_scope.
Local Open Scope N.

Section Var.
  Import ExprNotations.

  Context {var : tvar}.

  Definition sha_round := BitVec 7.
  Definition sha_word := BitVec 32.
  Definition sha_block := Vec sha_word 16.
  Definition sha_digest := Vec sha_word 8.

  Definition padder_waiting := Constant (BitVec 4) 0.
  Definition padder_emit_bit := Constant (BitVec 4) 1.
  Definition padder_flushing := Constant (BitVec 4) 2.
  Definition padder_writing_length := Constant (BitVec 4) 3.

  (* SHA-256 message padding *)
  (* - Padder expects data to packed (no gaps), except the final word.
     - The last word must also assert is_final, and have final_length set.

     Padder routine states:
     - padder_waiting : More data coming - default state
     - padder_emit_bit : Emit final bit before length, this state only occurs when final_length = 4, as with other lengths
                         there is space for the bit to be emitted during padder_waiting state
                         This is the 1 bit appended to a message as defined in section 5.1.1 of FIPS 180-4
     - padder_flushing : Emit 0 words until we reach the last two words of the block
     - padder_writing_length :  Write the length to the last two words
   *)
  Definition sha256_padder : Circuit _ [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit] (Bit ** sha_word ** Bit) :=
    {{
    fun data_valid data is_final final_length consumer_ready clear =>
    (* offset, is the offset in the current block 0 <= offset < 16 *)
    let/delay '(done, out, out_valid, state, length; current_offset) :=
      if clear
      then `Constant (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 4)
                     (true, (0, (false, (0, (0, 0)))))`
      else if !consumer_ready then (done, out, out_valid, state, length, current_offset)
      else

      let next_state :=
        if is_final && state == `padder_waiting` then
          (* From our receiving state we can transition to: *)
          (* - Emitting 0x80.. state if final word was a full word *)
          if final_length == `K 4` then `padder_emit_bit`
          (* - Writing length directly if we there 2 words left in this block *)
          else if current_offset == `K 13`
          then `padder_writing_length`
          (* - Writing padding 0's *)
          else `padder_flushing`
        else if state == `padder_emit_bit` then
          (* If we are at offset 13, switch to writing length as there is space
             this block for the length *)
          if current_offset == `K 13`
          then `padder_writing_length`
          else `padder_flushing`
        else if state == `padder_flushing` then
          (* If we are at offset 13, switch to writing length as there is space
             this block for the length *)
          if current_offset == `K 13`
          then `padder_writing_length`
          else `padder_flushing`
        else if state == `padder_writing_length` then
          if current_offset == `K 15`
          then `padder_waiting`
          else `padder_writing_length`
        else
          state
        in

      let next_length :=
        if state == `padder_waiting` && is_final then length + `bvresize 61` final_length
        else if state == `padder_waiting` && data_valid then length + `K 4`
        (* We are done here so set the next length to 0 *)
        else if state == `padder_writing_length` && current_offset == `K 15`
          then `K 0`
        else length
        in

      let next_out :=
        (* If we have final word and its not a full word, we can emit 0x80 byte
         * immediately *)
        if state == `padder_waiting` && is_final then
          if final_length == `K 0`
          then `Constant (BitVec 32) 0x80000000`
          else if final_length == `K 1`
          then `bvconcat` (`bvslice 24 8` data) (`Constant (BitVec 24) 0x800000`)
          else if final_length == `K 2`
          then `bvconcat` (`bvslice 16 16` data) (`Constant (BitVec 16) 0x8000`)
          else if final_length == `K 3`
          then `bvconcat` (`bvslice 8 24` data) (`Constant (BitVec 8) 0x80`)
          else data
        else if state == `padder_waiting` && data_valid then
          data
        else if state == `padder_emit_bit` then
          `Constant (BitVec 32) 0x80000000`
        else if state == `padder_writing_length` then
          if current_offset == `K 14`
          then `bvslice 32 32` (`bvresize 64` length << 3)
          else `bvslice 0 32` (`bvresize 64` length << 3)

        else `K 0`
      in

      let out_valid :=
        !(state == `padder_waiting` && (!data_valid) && (!is_final) ) in

      let next_offset :=
        if !out_valid then current_offset
        else (current_offset + `K 1`) (* addition mod 16 *) in

      let next_done :=
        !data_valid && (
        done || (state == `padder_writing_length` && next_state == `padder_waiting`)) in

      ( next_done
      , next_out, out_valid, next_state, next_length, next_offset)

      initially
        (true,(0,(false,(0,(0,0)))))
        : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 4)
        in

    (out_valid, out, done)
  }}.

  (* SHA-256 initial digest *)
  Definition sha256_initial_digest : denote_type sha_digest :=
    [ 0x6a09e667 ; 0xbb67ae85 ; 0x3c6ef372 ; 0xa54ff53a
    ; 0x510e527f ; 0x9b05688c ; 0x1f83d9ab ; 0x5be0cd19 ]%list.

  (* SHA-256 round constants *)
  Definition sha256_round_constants : Circuit [] [sha_round] sha_word := {{
    fun i =>
    let k :=
    `
    Constant (Vec sha_word 64) (
    [ 0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5
    ; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5
    ; 0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3
    ; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174
    ; 0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc
    ; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da
    ; 0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7
    ; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967
    ; 0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13
    ; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85
    ; 0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3
    ; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070
    ; 0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5
    ; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3
    ; 0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208
    ; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 ]%list
    )
    ` in
    `index` k i
  }}.

  Definition rotr n : Circuit _ [sha_word] sha_word :=
    {{ fun w =>  ((w >> n) | (w << (32 - n))) }}.

  (* SHA-256 message schedule update *)
  Definition sha256_message_schedule_update : Circuit _ [sha_word; sha_word; sha_word; sha_word] sha_word := {{
    fun w0 w1 w9 w14 =>
    let sum0 := (`rotr 7` w1) ^ (`rotr 18` w1) ^ (w1 >> 3) in
    let sum1 := (`rotr 17` w14) ^ (`rotr 19` w14) ^ (w14 >> 10) in
    w0 + sum0 + w9 + sum1
  }}%nat.

  (* SHA-256 compression function *)
  Definition sha256_compress : Circuit []%circuit_type [sha_digest; sha_word; sha_word]%circuit_type sha_digest := {{
    fun current_digest k w =>
    let '( a', b', c', d', e', f', g'; h' ) := `vec_as_tuple (n:=7)` current_digest in

    let s1 := (`rotr 6` e') ^ (`rotr 11` e') ^ (`rotr 25` e') in
    let ch := (e' & f') ^ (~e' & g') in
    let temp1 := (h' + s1 + ch + k + w) in
    let s0 := (`rotr 2` a') ^ (`rotr 13` a') ^ (`rotr 22` a') in
    let maj := (a' & b') ^ (a' & c') ^ (b' & c') in
    let temp2 := s0 + maj in

    (temp1 + temp2) :> a' :> b' :> c' :> (d' + temp1) :> e' :> f' :> g' :> []
  }}%nat.

  (* SHA-256 inner core *)
  (* `initial_digest` must be held until done *)
  Definition sha256_inner : Circuit _ [Bit; sha_block; sha_digest; Bit] (sha_digest ** Bit) :=
    {{
    fun block_valid block initial_digest clear =>

    let/delay '(current_digest, message_schedule, done; round) :=

      let inc_round := !done in
      let start := (* done && *) block_valid in

      let k_i := `sha256_round_constants` round in
      let '(w0,w1, _, _, _, _, _, _
           , _,w9, _, _, _, _,w14;_ ) := `vec_as_tuple (n:=15)` message_schedule in
      let update_schedule := round >= `K 15` in
      let w16 :=
        if update_schedule
        then `sha256_message_schedule_update` w0 w1 w9 w14
        else `index` message_schedule round in
      let w :=
        if update_schedule
        then message_schedule <<+ w16
        else message_schedule in

      let next_digest := `sha256_compress` current_digest k_i
        (`index` message_schedule (
          if round >= `K 16`
          then `K 15`
          else round)
        ) in

      let next_done := (round == `K 63`) || done in
      let round := if inc_round then round + `K 1` else round in

      if clear
      then `Constant (sha_digest ** sha_block ** Bit ** sha_round)
            (sha256_initial_digest, (repeat 0 16, (true, 0)))`
      else if start
           then (initial_digest, block, `Constant (Bit**sha_round) (false, 0)`)
           else if done then (current_digest, message_schedule, next_done, round)
                else (next_digest, w, next_done, round)

      initially (((sha256_initial_digest, (repeat 0 16, (true, 0))))
      : denote_type (sha_digest ** sha_block ** Bit ** sha_round )) in

    let updated_digest := `map2 {{fun a b => ( a + b ) }}` initial_digest current_digest in
    (updated_digest, done)

  }}.

  (* SHA-256 core *)
  (* returns (digest_valid, digest, ready) *)
  (* Data must only be passed when ready is asserted *)
  Definition sha256 : Circuit _ [Bit; sha_word; Bit; BitVec 4; Bit] (Bit ** sha_digest ** Bit) :=

    let reset_state : denote_type (Bit ** sha_block ** sha_digest ** BitVec 6 ** Bit) :=
      (true, (repeat 0 16, (sha256_initial_digest, (0, true)))) in

    {{ fun fifo_data_valid fifo_data is_final final_length clear =>

      (* 'count' runs from 0 to 17:
         - 0 - 15 are the padding cycles
         - 16 - the block is ready and sha_inner starts
         - 17 - is held until inner is done, then digest is stored and counter is reset
      *)

      let/delay '(ready, block, digest, count; done) :=
        let starting := fifo_data_valid && done in
        let ready_to_accept := `K 15` >= count in
        let block_ready := `K 16` == count in

        let '(padder_valid, padded_data; padder_done) :=
          `sha256_padder` fifo_data_valid fifo_data is_final final_length ready_to_accept clear in

        let '(inner_digest; inner_done) := `sha256_inner` block_ready block digest clear in

        let next_block :=
          if padder_valid && ready_to_accept
          then block <<+ padded_data
          else block in

        (* as above:
           count < 16 : increment when receieving
           count == 16 : increment immediately (adding a cycle for easier sync between padding and inner
           count == 17 : increment when inner is done
        *)
        let next_count : BitVec 6 :=
          if padder_valid && ready_to_accept then count + `K 1`
          else if `K 16` == count then `K 17`
          else if `K 17` == count && inner_done then `K 0`
          else count
        in

        (* only store the digest when the inner core is done *)
        let next_digest :=
          if starting then `Constant _ sha256_initial_digest`
          else if `K 17` == count && inner_done then inner_digest
          else digest in

        (* ready *)
        let signal_ready := `K 15` >= next_count in

        if clear then `Constant _ reset_state` else
        (signal_ready, next_block, next_digest, next_count, (padder_done && inner_done && count == `K 0` ) )

        initially reset_state in

       (done, digest, ready)
    }}.

End Var.
