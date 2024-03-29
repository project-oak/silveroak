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
Require Import Cava.Components.Fifo.
Require Import Cava.Components.RealignMasked.

Import ListNotations.
Import PrimitiveNotations.

Local Open Scope string_scope.
Local Open Scope N.

Section Var.
  Import ExprNotations.

  Context {var : tvar}.

  Definition realign_masked_fifo_local_state :=
    (Bit ** Bit ** BitVec 32 ** BitVec 4 ** Bit ** Bit)%circuit_type.

  Definition realign_masked_fifo_state fifo_size :=
    (realign_masked_fifo_local_state **
     realign_state ** fifo_state (BitVec 32) fifo_size)%circuit_type.

  Definition realign_masked_fifo fifo_size:
    Circuit (realign_masked_fifo_state fifo_size)
            [Bit; BitVec 32; BitVec 4; Bit; Bit]
            (Bit ** BitVec 32 ** BitVec 4 ** Bit ** Bit ) := {{
    fun data_valid data data_mask drain consumer_ready =>

    let/delay '(is_last, out_valid, out_data, out_length, fifo_empty; fifo_full) :=
      let '(realign_valid, realign_data; realign_length) :=
        `realign` (data_valid && ! drain) data data_mask (drain && fifo_empty && consumer_ready) (!fifo_full) in

      let '(fifo_valid, fifo_data, fifo_empty; fifo_full) :=
        `fifo fifo_size` (realign_valid && (! drain) && (!fifo_full) ) realign_data consumer_ready in

      let valid :=
        if drain then fifo_valid || realign_valid else fifo_valid in
      let data :=
        if drain && !fifo_valid then realign_data
        else fifo_data in
      let length :=
        if drain && !fifo_valid then realign_length
        else `K 4` in

      (drain && !fifo_valid && valid, valid, data, length, fifo_empty, fifo_full)
      initially (false, (false, (0, (0, (true, false)))))
      : denote_type realign_masked_fifo_local_state
    in
    (out_valid, out_data, out_length, is_last, fifo_full)
  }}.

End Var.
