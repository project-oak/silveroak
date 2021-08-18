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

  Definition sha256_padder : Circuit _ [Bit; BitVec 32; Bit; BitVec 4; Bit; Bit] (Bit ** sha_word ** Bit ** Bit) :=
    {{
    fun data_valid data is_final final_length consumer_ready clear =>
    (* offset, is the offset in the current block 0 <= offset < 16 *)
    let/delay '(done, out, out_valid, state, length; current_offset) :=
      if clear
      then `Constant (Bit ** sha_word ** Bit ** BitVec 4 ** BitVec 61 ** BitVec 16)
                     (1, (0, (0, (0, (0, 0)))))`
      else if !consumer_ready then (done, out, out_valid, state, length, current_offset)
      else

      let next_state :=
        if is_final & state == `padder_waiting` then
          (* From our receiving state we can transition to: *)
          (* - Emitting 0x80.. state if final word was a full word *)
          if final_length == `K 4` then `padder_emit_bit`
          (* - Writing length directly if we there 2 words left in this block *)
          else if current_offset == `K 13`
          then `padder_writing_length`
          (* - Writing padding 0's *)
          else `padder_flushing`
        else if state == `padder_emit_bit` then
          `padder_flushing`
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
        if state == `padder_waiting` & is_final then length + `bvresize 61` final_length
        else if state == `padder_waiting` & data_valid then length + `K 4`
        (* We are done here so set the next length to 0 *)
        else if state == `padder_writing_length` & current_offset == `K 15`
          then `K 0`
        else length
        in

      let next_out :=
        (* If we have final word and its not a full word, we can emit 0x80 byte
         * immediately *)
        if state == `padder_waiting` & is_final then
          if final_length == `K 0`
          then `Constant (BitVec 32) 0x80000000`
          else if final_length == `K 1`
          then `bvconcat` (`bvslice 24 8` data) (`Constant (BitVec 24) 0x800000`)
          else if final_length == `K 2`
          then `bvconcat` (`bvslice 16 16` data) (`Constant (BitVec 16) 0x8000`)
          else if final_length == `K 3`
          then `bvconcat` (`bvslice 8 24` data) (`Constant (BitVec 8) 0x80`)
          else data
        else if state == `padder_waiting` & data_valid then
          data
        else if state == `padder_emit_bit` then
          `Constant (BitVec 32) 0x80000000`
        else if state == `padder_writing_length` then
          if current_offset == `K 14`
          then `bvslice 32 32` (length << 3)
          else `bvslice 0 32` (length << 3)

        else `K 0`
      in

      let out_valid :=
        !(state == `padder_waiting` & (!data_valid) & (!is_final) ) in

      let next_offset :=
        if !out_valid then current_offset
        else if current_offset == `K 15` then `K 0`
        else (current_offset + `K 1`) in

      let next_done :=
        !data_valid & (
        done | (state == `padder_writing_length` & next_state == `padder_waiting`)) in

      ( next_done
      , next_out, out_valid, next_state, next_length, next_offset)

      initially
        (1,(0,(0,(0,(0,0)))))
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

      let next_done := (round == `K 63`) | done in
      let round := if inc_round then round + `K 1` else round in

      if clear
      then `Constant (sha_digest ** sha_block ** Bit ** sha_round)
            (sha256_initial_digest, (repeat 0 16, (1, 0)))`
      else if start
           then (initial_digest, block, `Constant (Bit**sha_round) (0, 0)`)
           else if done then (current_digest, message_schedule, next_done, round)
                else (next_digest, w, next_done, round)

      initially (((sha256_initial_digest, (repeat 0 16, (1, 0))))
      : denote_type (sha_digest ** sha_block ** Bit ** sha_round )) in

    let updated_digest := `map2 {{fun a b => ( a + b ) }}` initial_digest current_digest in
    (updated_digest, done)

  }}.

  (* SHA-256 core *)
  (* returns (digest_valid, digest, ready) *)
  (* Data must only be passed when ready is asserted *)
  Definition sha256 : Circuit _ [Bit; sha_word; Bit; BitVec 4; Bit] (Bit ** sha_digest ** Bit) :=

    let reset_state : denote_type (Bit ** sha_block ** sha_digest ** BitVec 6 ** Bit) :=
      (1, (repeat 0 16, (sha256_initial_digest, (0, 1)))) in

    {{ fun fifo_data_valid fifo_data is_final final_length clear =>

      (* 'count' runs from 0 to 17:
         - 0 - 15 are the padding cycles
         - 16 - the block is ready and sha_inner starts
         - 17 - is held until inner is done, then digest is stored and counter is reset
      *)

      let/delay '(padder_ready, block, digest, count; done) :=
        let starting := fifo_data_valid & done in
        let ready_to_accept := `K 15` >= count in
        let block_ready := `K 16` == count in

        let '(padder_valid, padded_data, padder_ready; padder_done) :=
          `sha256_padder` fifo_data_valid fifo_data is_final final_length ready_to_accept clear in

        let '(inner_digest; inner_done) := `sha256_inner` block_ready block digest clear in

        let next_block :=
          if padder_valid & ready_to_accept
          then block <<+ padded_data
          else block in

        (* as above:
           count < 16 : increment when receieving
           count == 16 : increment immediately (adding a cycle for easier sync between padding and inner
           count == 17 : increment when inner is done
        *)
        let next_count : BitVec 6 :=
          if padder_valid & ready_to_accept then count + `K 1`
          else if `K 16` == count then `K 17`
          else if `K 17` == count & inner_done then `K 0`
          else count
        in

        (* only store the digest when the inner core is done *)
        let next_digest :=
          if starting then `Constant _ sha256_initial_digest`
          else if `K 17` == count & inner_done then inner_digest
          else digest in

        if clear then `Constant _ reset_state` else
        (padder_ready, next_block, next_digest, next_count, (padder_done & inner_done & count == `K 0` ) )

        initially reset_state in

       (done, digest, padder_ready)
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
    step sha256_inner default (1, (sha256_test_block, (sha256_initial_digest, (0, tt)))).

  Definition pp {n} (v: denote_type (Vec (BitVec 32) n)) :=
    List.map HexString.of_N v.

  (* Padding "abc" results in expected block. *)
  Goal
    simulate sha256_padder
    ([(1, (0x61626300, (1, (3, (1, (0, tt))))))] ++
      repeat (0, (0x99999999, (0, (0, (1, (0, tt)))))) 16
      ) =
    [ (1, (1633837952, (1, 0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (0, (1,0)))
    ; (1, (24, (1,1)))
    ; (0, (0, (1,1)))
    ].
  Proof. vm_compute. reflexivity. Qed.

  (* Inner state holds the correct values after 64 rounds. *)
  Goal
    fst (snd (simulate' sha256_inner (repeat (0, ([], (sha256_initial_digest, (0, tt)))) 64) (fst init))) =
    [0x506E3058; 0xD39A2165; 0x04D24D6C; 0xB85E2CE9; 0x5EF50F24; 0xFB121210; 0x948D25B6; 0x961F4894].
  Proof. vm_compute. reflexivity. Qed.

  (* Output is the correct message digest *)
  Goal
    fst (last (fst (simulate' sha256_inner (repeat (0, ([], (sha256_initial_digest, (0, tt)))) 64) (fst init))) default) =
    [0xBA7816BF; 0x8F01CFEA; 0x414140DE; 0x5DAE2223; 0xB00361A3; 0x96177A9C; 0xB410FF61; 0xF20015AD ].
  Proof. vm_compute. reflexivity. Qed.

  (* sha256 "abc" = sha256 (0x61626300 @ byte mask 0xFFFFFF00) = correct digest *)
  Goal
    last (

    simulate sha256 (
       (1, (0x61626300, (1, (3, (0, tt))))) ::
       repeat (0, (0, (0, (0, (0, tt))))) (81)
      )
    ) default
    = (1, ([0xBA7816BF; 0x8F01CFEA; 0x414140DE; 0x5DAE2223; 0xB00361A3; 0x96177A9C; 0xB410FF61; 0xF20015AD ], 1)).
  Proof. vm_compute; reflexivity. Qed.

  (* pad two blocks correctly *)
  Goal
    List.map (fun x => fst (snd x)) (
    simulate sha256_padder (
       (List.map (fun data =>
         (* data_valid data is_final final_length consumer_ready clear *)
         (1, (data, (0, (0, (1, (0, tt))))))
       )
       [ 0x61626364
       ; 0x62636465
       ; 0x63646566
       ; 0x64656667
       ; 0x65666768
       ; 0x66676869
       ; 0x6768696A
       ; 0x68696A6B
       ; 0x696A6B6C
       ; 0x6A6B6C6D
       ; 0x6B6C6D6E
       ; 0x6C6D6E6F
       ; 0x6D6E6F70
       ; 0x6E6F7071
       ])
       ++ [ (1, (0, (1, (0, (1, (0, tt))))))]
       ++ repeat (0, (0, (0, (0, (1, (0, tt)))))) (32 - 15)
      ))
    =
       (* block 1 *)
       [ 0x61626364 ; 0x62636465 ; 0x63646566 ; 0x64656667
       ; 0x65666768 ; 0x66676869 ; 0x6768696A ; 0x68696A6B
       ; 0x696A6B6C ; 0x6A6B6C6D ; 0x6B6C6D6E ; 0x6C6D6E6F
       ; 0x6D6E6F70 ; 0x6E6F7071 ; 0x80000000 ; 0x00000000

       (* block 2 *)
       ; 0x00000000 ; 0x00000000 ; 0x00000000 ; 0x00000000
       ; 0x00000000 ; 0x00000000 ; 0x00000000 ; 0x00000000
       ; 0x00000000 ; 0x00000000 ; 0x00000000 ; 0x00000000
       ; 0x00000000 ; 0x00000000 ; 0x00000000 ; 0x000001C0
       ].
  Proof. vm_compute; reflexivity. Qed.

  (* sha256 double block = correct digest *)
  Goal
    fst (snd
    (last (
    simulate sha256 (
       (List.map (fun data =>
         (1, (data, (0, (0, (0, tt)))))
       )
       [ 0x61626364
       ; 0x62636465
       ; 0x63646566
       ; 0x64656667
       ; 0x65666768
       ; 0x66676869
       ; 0x6768696A
       ; 0x68696A6B
       ; 0x696A6B6C
       ; 0x6A6B6C6D
       ; 0x6B6C6D6E
       ; 0x6C6D6E6F
       ; 0x6D6E6F70
       ; 0x6E6F7071
       ])
       ++ [
       (1, (0, (1, (0, (0, tt)))))]
       ++
          repeat (0, (0, (0, (0, (0, tt))))) (80*2)
      )
      ) default))
    =
    [ 0x248D6A61
      ; 0xD20638B8
      ; 0xE5C02693
      ; 0x0C3E6039
      ; 0xA33CE459
      ; 0x64FF2167
      ; 0xF6ECEDD4
      ; 0x19DB06C1
      ].
  Proof. vm_compute; reflexivity. Qed.

  (* sha256 double block = correct digest *)
  Goal
     fst (snd (last (simulate sha256 (
       (List.map (fun data => (1, (data, (0, (0, (0, tt))))))
       [
         0x36373435
       ; 0x32333031
       ; 0x3E3F3C3D
       ; 0x3A3B3839
       ; 0x26272425
       ; 0x22232021
       ; 0x2E2F2C2D
       ; 0x2A2B2829

       ; 0x16171415
       ; 0x12131011
       ; 0x1E1F1C1D
       ; 0x1A1B1819
       ; 0x06070405
       ; 0x02030001
       ; 0x0E0F0C0D
       ; 0x0A0B0809
       ])

       (* Note we are not observing the sha block outputs, but if we were
          we would see that it is not immediately ready to receive input here *)
       ++ repeat (0, (0, (0, (0, (0, tt))))) 80
       ++

       (List.map (fun data => (1, (data, (0, (0, (0, tt))))))
       [
         0x53616D70
       ; 0x6C65206D
       ; 0x65737361
       ; 0x67652066
       ; 0x6F72206B
       ; 0x65796C65
       ; 0x6E3D626C
       ; 0x6F636B6C
       ])
       ++ [ (1, (0x656E0000, (1, (2, (0, tt)))))]
       ++ repeat (0, (0, (0, (0, (0, tt))))) 80
      ) ) default))

    =
    [ 0xC0918E14
    ; 0xC43562B9
    ; 0x10DB4B81
    ; 0x01CF8812
    ; 0xC3DA2783
    ; 0xC670BFF3
    ; 0x4D88B3B8
    ; 0x8E731716 ]
      .
  Proof. vm_compute; reflexivity. Qed.

End SanityCheck.
