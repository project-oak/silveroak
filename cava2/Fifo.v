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
Require Import Coq.Arith.PeanoNat.
Require Import Cava.Util.List.

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

  Definition fifo {T} fifo_size: Circuit _ [Bit; T; Bit]
    (* out_valid, out, full *)
    (Bit ** T ** Bit ** Bit) :=
    let fifo_bits := BitVec (Nat.log2_up (fifo_size + 1)) in
    {{
    fun data_valid data accepted_output =>

    let/delay '(valid, output, fifo; count) :=
      let decrement := accepted_output && count >= `K 1` in

      ( count >= `K 1`
      , `index` fifo (count - `K 1`)

      , if data_valid then data +>> fifo else fifo
      , if data_valid && !decrement then count + `K 1`
        else if !data_valid && decrement then (count - `K 1`)
        else count
      )

      initially (false,(default,(@default (Vec T fifo_size), 0)))
      : denote_type (Bit ** T ** Vec T fifo_size ** fifo_bits) in

    ( valid, if valid then output else `Constant T default`
    (* Will be empty if accepted_output is asserted next cycle *)
    , (count == `Constant fifo_bits 0` )
    (* We are full, does not assume output this cycle has been accepted yet *)
    , (count == `Constant fifo_bits (N.of_nat fifo_size)` ) )
  }}.

  Definition realign_inner : Circuit _ [BitVec 32; BitVec 4; BitVec 32; BitVec 4] (BitVec 64 ** BitVec 4) :=
  {{ fun existing existing_len data data_mask =>
      let '(packed_data; packed_len) :=
        (* Contiguous bytes only *)
             if data_mask == `K 0x0` then (`K 0`, `K 0`)
        else if data_mask == `K 0x1` then ((data << 24) & (`K 0xFF000000`), `K 1`)
        else if data_mask == `K 0x2` then ((data << 16) & (`K 0xFF000000`), `K 1`)
        else if data_mask == `K 0x4` then ((data << 8 ) & (`K 0xFF000000`), `K 1`)
        else if data_mask == `K 0x8` then ((data      ) & (`K 0xFF000000`), `K 1`)
        else if data_mask == `K 0x3` then ((data << 16) & (`K 0xFFFF0000`), `K 2`)
        else if data_mask == `K 0x6` then ((data << 8 ) & (`K 0xFFFF0000`), `K 2`)
        else if data_mask == `K 0xC` then ((data      ) & (`K 0xFFFF0000`), `K 2`)
        else if data_mask == `K 0x9` then ((data << 8 ) & (`K 0xFFFFFF00`), `K 3`)
        else if data_mask == `K 0xE` then ((data      ) & (`K 0xFFFFFF00`), `K 3`)
        (* else if data_mask == `K 0xF` then *) else (data, `K 4`)
      in
      (* FIXME: this solves type unifcation *)
      let _ : BitVec 32 := packed_data in
      let out : BitVec 64 :=
        if existing_len == `K 0x0` then
              `bvconcat` packed_data `Constant (BitVec 32) 0`
        else if existing_len == `K 0x1` then
              `bvconcat` (`bvconcat` ( `bvslice 24 8` existing) packed_data) `Constant (BitVec 24) 0`
        else if existing_len == `K 0x2` then
              `bvconcat` (`bvconcat` ( `bvslice 16 16` existing) packed_data) `Constant (BitVec 16) 0`
        (* else if existing_len == `K 0x3` then *) else
              (`bvconcat` (`bvconcat` ( `bvslice 8 24` existing) packed_data) `Constant (BitVec 8) 0`)
      in
      (out, packed_len + existing_len)
  }}.

  Definition realign: Circuit _ [Bit; BitVec 32; BitVec 4; Bit; Bit] (Bit ** BitVec 32 ** BitVec 4) := {{

    fun data_valid data data_mask flush consumer_ready =>

    let/delay '(out_valid, out, out_length, queue; length) :=
      if !consumer_ready
      then (out_valid, out, out_length, queue, length)
      else

        let out := `bvslice 32 32` queue in
        let out_valid := length >= `K 4` in
        let out_length := `bvresize 4` (`bvmin` length `K 4`) in

        let '(queue'; length') :=
          if out_valid || flush
          then (`bvslice 0 32` queue, if length >= `K 4` then length - `K 4` else `K 0`)
          else (`bvslice 32 32` queue, length) in

        let '(next_queue; next_length) :=

          if data_valid && !flush then `realign_inner` queue' length' data data_mask
          else (`bvconcat` queue' `K 0`, length')
        in

        let valid_or_flushing :=
          out_valid || (flush && length >= `K 1`) in

        (valid_or_flushing, out, out_length, next_queue, next_length)
        initially default
    in
    (out_valid, out, out_length)
  }}.

  Definition realign_fifo fifo_size: Circuit _ [Bit; BitVec 32; BitVec 4; Bit; Bit]
    (* *)
    (Bit ** BitVec 32 ** BitVec 4 ** Bit ** Bit ) := {{
    fun data_valid data data_mask drain consumer_ready =>

    let/delay '(is_last, out_valid, out_data, out_length, fifo_empty; fifo_full) :=
      let '(realigned_valid, realigned_data; realigned_length) :=
        `realign` data_valid data data_mask (drain && fifo_empty && consumer_ready) (!fifo_full) in

      let '(fifo_valid, fifo_data, fifo_empty; fifo_full) :=
        `fifo fifo_size` (realigned_valid && (! drain)) realigned_data consumer_ready in

      let valid :=
        if drain then fifo_valid || realigned_valid else fifo_valid in
      let data :=
        if drain && !fifo_valid then realigned_data
        else fifo_data in
      let length :=
        if drain && !fifo_valid then realigned_length
        else `K 4` in

      (drain && !fifo_valid && valid, valid, data, length, fifo_empty, fifo_full)
      initially default
    in
    (out_valid, out_data, out_length, is_last, fifo_full)
  }}.

End Var.
