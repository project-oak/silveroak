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

Require Import Cava.Util.Byte.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.
Require Import Cava.TLUL.
Require Import Cava.Invariant.

Require Import HmacHardware.Hmac.
Require Import HmacSpec.SHA256Properties.

Import ListNotations.

Section HmacSpec.

  Inductive HmacHwStates := Idle|Busy|Done.
  Print HmacHwStates.

  Local Notation HmacSpecRepr :=
    ( list Byte.byte
    * list Byte.byte
    * list N
    * HmacHwStates
    )%type.

  (* axiom to temporarily block update_repr *)
  Axiom update_repr': HmacSpecRepr -> HmacSpecRepr.

  Instance sha256_specification
  : specification_for hmac HmacSpecRepr := {|
      reset_repr := ([], [], repeat 0%N hmac_register_count, Idle);
      update_repr :=
        fun (input : denote_type (input_of hmac)) '(waiting_fifo, consumed_fifo, registers, state) =>
          let '(write_en,
                (write_data, (write_address, (write_mask, (is_fifo_write, _))))) := input
          in

          (* TODO *)
          update_repr' (waiting_fifo, consumed_fifo, registers, state);
      precondition :=
        fun (input : denote_type (input_of hmac)) '(waiting_fifo, consumed_fifo, registers, state) =>

          (* TODO *)
          True;

      postcondition :=
        fun (input : denote_type (input_of hmac)) '(waiting_fifo, consumed_fifo, registers, state)
          (output : denote_type (Vec (BitVec 32) hmac_register_count))
          =>
          let '(write_en,
                (write_data, (write_address, (write_mask, (is_fifo_write, _))))) := input
          in

          (* TODO *)
          exists digest : list N,
          (* the digest starts at address 0x11 *)
          List.slice 0%N output 0x11 8 = digest
          /\ match state with
             | Done => digest = BigEndianBytes.bytes_to_Ns 4 (SHA256.sha256 consumed_fifo)
             | _ => True
             end
    |}.
End HmacSpec.
