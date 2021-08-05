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

Require Import Cava.Fifo.

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

  Definition padder_waiting := Constant (0: denote_type (BitVec 4)).
  Definition padder_emit_bit := Constant (1: denote_type (BitVec 4)).
  Definition padder_flushing := Constant (2: denote_type (BitVec 4)).
  Definition padder_writing_length := Constant (3: denote_type (BitVec 4)).

  (* SHA-256 message padding *)
  Definition sha256_padder : Circuit _ [Bit; BitVec 32; Bit; BitVec 4; Bit] (Bit ** sha_word ** Bit) :=
    {{
    fun data_valid data final final_byte_length back_pressure =>
    let/delay '(done, out, out_valid, state, length; current_offset) :=
      if !back_pressure
      then (done, out, out_valid, state, length, current_offset)
      else

      let next_state :=
        if final && state == `padder_waiting` then
          if final_byte_length == `K 4`
          then `padder_emit_bit`
          else `padder_flushing`
        else if state == `padder_emit_bit` then
          `padder_flushing`
        else if state == `padder_flushing` then
          if current_offset == `K 61`
          then `padder_writing_length`
          else `padder_flushing`
        else if state == `padder_writing_length` then
          if current_offset == `K 63`
          then `padder_waiting`
          else `padder_writing_length`
        else
          state
        in

      let next_length :=
        if state == `padder_waiting` && data_valid then length + `K 4`
        else if state == `padder_waiting` && final then length + `resize` final_byte_length
        else if state == `padder_writing_length` && current_offset == `K 62`
          then `K 0`
        else length
        in

      let next_out :=
        if state == `padder_waiting` && final then
          if final_byte_length == `K 0`
          then `Constant (0x00000001: denote_type (BitVec 32))`
          else if final_byte_length == `K 1`
          then `slice 0 8` data ++ `Constant (0x000001: denote_type (BitVec 24))`
          else if final_byte_length == `K 2`
          then `slice 0 16` data ++ `Constant (0x0001: denote_type (BitVec 16))`
          else if final_byte_length == `K 3`
          then `slice 0 24` data ++ `Constant (0x01: denote_type (BitVec 8))`
          else data
        else if state == `padder_waiting` && data_valid then
          data
        else if state == `padder_emit_bit` then
          `Constant (0x00000001: denote_type (BitVec 32))`
        else if state == `padder_writing_length` then
          if current_offset == `K 62`
          then `reverse` (`slice 32 32` length)
          else `reverse` (`slice 0 32` length)

        else `K 0`
      in

      let step :=
        (state == `padder_waiting` && (data_valid || final))
        || (! (state == `padder_waiting`) ) in

      let next_offset := if step then current_offset + `K 1` else current_offset in

      ( state == `padder_writing_length` && next_state == `padder_waiting`
      , next_out, step, next_state, next_length, next_offset)

      initially
        (false,(0,(false,(0,(0,0)))))
        : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16)
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
    Constant (
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
    ; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 ]%list : denote_type (Vec sha_word 64)
    )
    ` in
    `index` k i
  }}.

  (* SHA-256 message schedule update *)
  Definition sha256_message_schedule_update : Circuit _ [sha_word; sha_word; sha_word; sha_word] sha_word := {{
    fun w0 w1 w9 w14 =>
    let sum0 := (w1 >>> `7`) ^ (w1 >>> `18`) ^ (w1 >> `3`) in
    let sum1 := (w14 >>> `17`) ^ (w14 >>> `19`) ^ (w14 >> `10`) in
    w0 + sum0 + w9 + sum1
  }}%nat.

  (* SHA-256 compression function *)
  Definition sha256_compress : Circuit []%circuit_type [sha_digest; sha_word; sha_word]%circuit_type sha_digest := {{
    fun current_digest k w =>
    let '( a', b', c', d', e', f', g'; h' ) := `vec_as_tuple (n:=7)` current_digest in

    let s1 := (e' >>> `6`) ^ (e' >>> `11`) ^ (e' >>> `25`) in
    let ch := (e' & f') ^ (~e' & g') in
    let temp1 := (h' + s1 + ch + k + w) in
    let s0 := (a' >>> `2`) ^ (a' >>> `13`) ^ (a' >>> `22`) in
    let maj := (a' & b') ^ (a' & c') ^ (b' & c') in
    let temp2 := s0 + maj in

    (temp1 + temp2) :> a' :> b' :> c' :> (d' + temp1) :> e' :> f' :> g' :> []
  }}%nat.

  (* SHA-256 core *)
  Definition sha256_inner : Circuit _ [Bit; sha_block; sha_digest] (sha_digest ** Bit) :=
    {{
    fun block_valid block initial_digest =>

    let/delay '(stored_digest, current_digest, message_schedule, done; round) :=

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

      let done := (round == `K 64`) || done in
      let round := if inc_round then round + `K 1` else round in

      if start
      then (initial_digest, initial_digest, block, `Constant ((false, 0):denote_type (Bit**sha_round))`)
      else if done then (stored_digest, current_digest, message_schedule, done, round)
      else (stored_digest, next_digest, w, done, round)

      initially ((sha256_initial_digest, (sha256_initial_digest, (repeat 0 16, (false, 0))))
      : denote_type (sha_digest ** sha_digest ** sha_block ** Bit ** sha_round )) in

    let updated_digest := `map2 {{fun a b => ( a + b ) }} ` stored_digest current_digest in
    (updated_digest, done)

  }}.

  (* SHA-256 core *)
  (* TODO(FIXME): *)
  Definition sha256 : Circuit _ [Bit; sha_word; Bit; BitVec 4] (Bit ** sha_digest ** Bit) :=
    {{ fun data_valid data final final_mask =>
       let '(padded_valid, padded_data; padder_done) := `sha256_padder` data_valid data final final_mask `False` in

       let/delay '(block, digest, count; busy) :=

         let accept_fifo := !busy in

         let '(fifo_valid, fifo_data; fifo_full) := `fifo (fifo_size := 999)` padded_valid padded_data accept_fifo in

         let new_data := fifo_valid && accept_fifo in

         let '(next_block;next_count) :=
           if new_data
           then (block <<+ fifo_data, count + `K 1`)
           else (block, count)
         in

         let block_valid := `False` in
         let '(inner_digest; inner_done) := `sha256_inner` block_valid block `Constant sha256_initial_digest` in

         let next_digest := if inner_done then inner_digest else digest in

         (next_block, inner_digest, next_count, busy)
         initially (repeat 0 16, (sha256_initial_digest, (0,false))): denote_type (sha_block ** sha_digest ** BitVec 4 ** Bit) in

       (busy, digest, busy)
    }}.

End Var.

Section SanityCheck.
  Require Import Cava.Semantics.
  Open Scope list_scope.

  Definition sha256_test_block : denote_type sha_block :=
    [ 0x61626380; 0x00000000; 0x00000000; 0x00000000
    ; 0x00000000; 0x00000000; 0x00000000; 0x00000000
    ; 0x00000000; 0x00000000; 0x00000000; 0x00000000
    ; 0x00000000; 0x00000000; 0x00000000; 0x00000018
    ].

  Definition init :=
    step sha256_inner default (true, (sha256_test_block, (sha256_initial_digest, tt))).

  Definition pp {n} (v: denote_type (Vec (BitVec 32) n)) :=
      List.map HexString.of_N v.

  (* Inner state holds the correct values after 64 rounds. *)
  Goal
    fst (snd (snd (simulate' sha256_inner (repeat (false, ([], ([], tt))) 64) (fst init)))) =
    [0x506E3058; 0xD39A2165; 0x04D24D6C; 0xB85E2CE9; 0x5EF50F24; 0xFB121210; 0x948D25B6; 0x961F4894].
  Proof. vm_compute. reflexivity. Qed.

  (* Output is the correct message digest *)
  Goal
    fst (last (fst (simulate' sha256_inner (repeat (false, ([], ([], tt))) 64) (fst init))) default) =
    [0xBA7816BF; 0x8F01CFEA; 0x414140DE; 0x5DAE2223; 0xB00361A3; 0x96177A9C; 0xB410FF61; 0xF20015AD ].
  Proof. vm_compute. reflexivity. Qed.

End SanityCheck.
