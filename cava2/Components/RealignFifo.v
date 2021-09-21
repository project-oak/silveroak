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
Require Import Cava.Components.Realigner.

Import ListNotations.
Import PrimitiveNotations.

Local Open Scope string_scope.
Local Open Scope N.

Section Var.
  Import ExprNotations.

  Context {var : tvar}.

  Definition realign_fifo fifo_size: Circuit _ [Bit; BitVec 32; BitVec 4; Bit; Bit]
    (* *)
    (Bit ** BitVec 32 ** BitVec 4 ** Bit ** Bit ) := {{
    fun data_valid data data_mask drain consumer_ready =>

    let/delay '(is_last, out_valid, out_data, out_length, fifo_empty; fifo_full) :=
      let '(realigned_valid, realigned_data; realigned_length) :=
        `realign` data_valid data data_mask (drain && fifo_empty && consumer_ready) (!fifo_full) in

      let '(fifo_valid, fifo_data, fifo_empty; fifo_full) :=
        `fifo fifo_size` (realigned_valid && (! drain) && (!fifo_full) ) realigned_data consumer_ready in

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
