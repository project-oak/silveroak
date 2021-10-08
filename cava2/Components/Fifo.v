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
    (* out_valid, out, empty, full *)
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
End Var.
