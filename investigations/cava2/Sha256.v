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

  Definition padder_waiting := Constant (BitVec 4) 0.
  Definition padder_emit_bit := Constant (BitVec 4) 1.
  Definition padder_flushing := Constant (BitVec 4) 2.
  Definition padder_writing_length := Constant (BitVec 4) 3.

  (* SHA-256 message padding *)
  Definition sha256_padder : Circuit _ [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit] (Bit ** sha_word ** Bit ** Bit) :=
    {{
    fun data_valid data is_final final_length consumer_ready clear =>
    let/delay '(done, out, out_valid, state, length; current_offset) :=
      if clear
      then `Constant (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16)
                     (false, (0, (false, (0, (0, 0)))))`
      else if !consumer_ready then (done, out, out_valid, state, length, current_offset)
      else

      let next_state :=
        if is_final && state == `padder_waiting` then
          if final_length == `K 4`
          then `padder_emit_bit`
          else `padder_flushing`
        else if state == `padder_emit_bit` then
          `padder_flushing`
        else if state == `padder_flushing` then
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
        if state == `padder_waiting` && is_final then length + `resize` final_length
        else if state == `padder_waiting` && data_valid then length + `K 4`
        else if state == `padder_writing_length` && current_offset == `K 15`
          then `K 0`
        else length
        in

      let next_out :=
        if state == `padder_waiting` && is_final then
          if final_length == `K 0`
          then `Constant (BitVec 32) 0x80000000`
          else if final_length == `K 1`
          then `Constant (BitVec 24) 0x800000` ++ `slice 24 8` data
          else if final_length == `K 2`
          then `Constant (BitVec 16) 0x8000` ++ `slice 16 16` data
          else if final_length == `K 3`
          then `Constant (BitVec 8) 0x80` ++ `slice 8 24` data
          else data
        else if state == `padder_waiting` && data_valid then
          data
        else if state == `padder_emit_bit` then
          `Constant (BitVec 32) 0x80000000`
        else if state == `padder_writing_length` then
          if current_offset == `K 14`
          then (`slice 32 32` (`Constant (BitVec 3) 0` ++ length))
          else (`slice 0 32` (`Constant (BitVec 3) 0` ++ length))

        else `K 0`
      in

      let step :=
        (state == `padder_waiting` && (data_valid || is_final))
        || (! (state == `padder_waiting`) ) in

      let next_offset := if step then current_offset + `K 1` else current_offset in

      ( state == `padder_writing_length` && next_state == `padder_waiting`
      , next_out, step, next_state, next_length, next_offset)

      initially
        (false,(0,(false,(0,(0,0)))))
        : denote_type (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16)
        in

    (out_valid, out, consumer_ready, done)
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

      let done := (round == `K 64`) || done in
      let round := if inc_round then round + `K 1` else round in

      if start || clear
      then (initial_digest, block, `Constant (Bit**sha_round) (false, 0)`)
      else if done then (current_digest, message_schedule, done, round)
      else (next_digest, w, done, round)

      initially (((sha256_initial_digest, (repeat 0 16, (true, 0))))
      : denote_type (sha_digest ** sha_block ** Bit ** sha_round )) in

    let updated_digest := `map2 {{fun a b => ( a + b ) }}` initial_digest current_digest in
    (updated_digest, done)

  }}.

  (* SHA-256 core *)
  Definition sha256 : Circuit _ [Bit; sha_word; Bit; BitVec 4; Bit] (Bit ** sha_digest ** Bit) :=
    {{ fun fifo_data_valid fifo_data is_final final_length clear =>

       let/delay '(inner_done_edge, accept_input, accept_padded, block, digest, count, received_last_byte; done) :=
         let starting := fifo_data_valid && done in

         let '(padded_valid, padded_data, padder_ready; padder_done) :=
           `sha256_padder` fifo_data_valid fifo_data is_final final_length accept_padded clear in

         let block_valid := count == `K 16` in
         let '(inner_digest; inner_done) := `sha256_inner` block_valid block digest clear in

         let next_accept_padded := padded_valid && inner_done in

         let '(next_block; next_count) :=
           if next_accept_padded
           then (block <<+ padded_data, count + `K 1`)
           else (block, `K 0`)
         in

         let q := !inner_done_edge && inner_done  in
         let next_received_last_byte := received_last_byte || is_final in
         let next_done := (!starting && !is_final) && (done || (received_last_byte && q))  in
         let next_digest := if q then inner_digest else digest in

         if ! clear then
         (inner_done, padder_ready, next_accept_padded, next_block, next_digest, next_count, next_received_last_byte,
         next_done)
         else
          `Constant (Bit ** Bit ** Bit ** sha_block ** sha_digest ** BitVec 6 ** Bit ** Bit)
                    (true, (true, (true, (repeat 0 16, (sha256_initial_digest, (0, (false, false)))))))`

         initially ((true, (true, (true, (repeat 0 16, (sha256_initial_digest, (0, (false, false))))))))
         : denote_type (Bit ** Bit ** Bit ** sha_block ** sha_digest ** BitVec 6 ** Bit ** Bit)
            in

       (done, digest, accept_input)
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
    step sha256_inner default (true, (sha256_test_block, (sha256_initial_digest, (false, tt)))).

  Definition pp {n} (v: denote_type (Vec (BitVec 32) n)) :=
      List.map HexString.of_N v.

  (* Padding "abc" results in expected block. *)
  Goal
    simulate sha256_padder
    ([(true, (0x61626300, (true, (3, (true, (false, tt))))))] ++
      repeat (false, (0x99999999, (false, (0, (true, (false, tt)))))) 16
      ) =
    [ (true, (1633837952, (true, false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (0, (true,false)))
    ; (true, (24, (true,true)))
    ; (false, (0, (true,false)))
    ].
  Proof. vm_compute. reflexivity. Qed.

  (* Inner state holds the correct values after 64 rounds. *)
  Goal
    fst (snd (simulate' sha256_inner (repeat (false, ([], (sha256_initial_digest, (false, tt)))) 64) (fst init))) =
    [0x506E3058; 0xD39A2165; 0x04D24D6C; 0xB85E2CE9; 0x5EF50F24; 0xFB121210; 0x948D25B6; 0x961F4894].
  Proof. vm_compute. reflexivity. Qed.

  (* Output is the correct message digest *)
  Goal
    fst (last (fst (simulate' sha256_inner (repeat (false, ([], (sha256_initial_digest, (false, tt)))) 64) (fst init))) default) =
    [0xBA7816BF; 0x8F01CFEA; 0x414140DE; 0x5DAE2223; 0xB00361A3; 0x96177A9C; 0xB410FF61; 0xF20015AD ].
  Proof. vm_compute. reflexivity. Qed.

  (* sha256 "abc" = sha256 (0x61626300 @ byte mask 0xFFFFFF00) = correct digest *)
  Goal
    fst (snd (last (simulate sha256 (
       (true, (0x61626300, (true, (3, (false, tt))))) ::
       repeat (false, (0, (false, (0, (false, tt))))) (64+19)
      )) default))
    = [0xBA7816BF; 0x8F01CFEA; 0x414140DE; 0x5DAE2223; 0xB00361A3; 0x96177A9C; 0xB410FF61; 0xF20015AD ].
  Proof. vm_compute. reflexivity. Qed.

End SanityCheck.
