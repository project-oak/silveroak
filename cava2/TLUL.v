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
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.List.

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.

Import ExprNotations.
Import PrimitiveNotations.

(* Naming and parameter choices follow OpenTitan conventions *)
(* As such, 'tl_h2d_t' 'tl_d2h_t' come from the OpenTitan naming *)
(* - 'h' refers to host *)
(* - 'd' refers to device *)


Definition TL_AW  := 32.
Definition TL_DW  := 32.
Definition TL_AIW := 8.
Definition TL_DIW := 1.
Definition TL_DUW := 4.
Definition TL_DBW := 4. (* (TL_DW>>3). *)
Definition TL_SZW := 2. (* $clog2($clog2(TL_DBW)+1). *)

(* (1* typedef struct packed { *1) *)
(* (1*   logic                         a_valid; *1)   1 *)
(* (1*   tl_a_op_e                     a_opcode; *1)  3 *)
(* (1*   logic                  [2:0]  a_param; *1)   3 *)
(* (1*   logic  [top_pkg::TL_SZW-1:0]  a_size; *1)    2 *)
(* (1*   logic  [top_pkg::TL_AIW-1:0]  a_source; *1)  8 *)
(* (1*   logic   [top_pkg::TL_AW-1:0]  a_address; *1) 32 *)
(* (1*   logic  [top_pkg::TL_DBW-1:0]  a_mask; *1)    4 *)
(* (1*   logic   [top_pkg::TL_DW-1:0]  a_data; *1)    32 *)
(* (1*   tl_a_user_t                   a_user; *1)    16 *)
(* (1*   logic                         d_ready; *1)   1 *)
(* (1* } tl_h2d_t; *1)
=102 *)
Definition tl_h2d_t : type :=
  Bit **
  BitVec 3 **
  BitVec 3 **
  BitVec TL_SZW **
  BitVec TL_AIW **
  BitVec TL_AW **
  BitVec TL_DBW **
  BitVec TL_DW **
  BitVec 16 **
  Bit.

(* typedef struct packed { *)
(*   logic                         d_valid; *)
(*   tl_d_op_e                     d_opcode; *)
(*   logic                  [2:0]  d_param; *)
(*   logic  [top_pkg::TL_SZW-1:0]  d_size; *)
(*   logic  [top_pkg::TL_AIW-1:0]  d_source; *)
(*   logic  [top_pkg::TL_DIW-1:0]  d_sink; *)
(*   logic   [top_pkg::TL_DW-1:0]  d_data; *)
(*   logic  [top_pkg::TL_DUW-1:0]  d_user; *)
(*   logic                         d_error; *)
(*   logic                         a_ready; *)
(* } tl_d2h_t; *)

Definition tl_d2h_t : type :=
  Bit **
  BitVec 3 **
  BitVec 3 **
  BitVec 2 **
  BitVec 8 **
  BitVec 1 **
  BitVec 32 **
  BitVec 4 **
  Bit **
  Bit.

Section Var.
  Import ExprNotations.
  Context {var : tvar}.

  Local Open Scope N.

  (* typedef enum logic [2:0] { *)
  (*   PutFullData    = 3'h 0, *)
  (*   PutPartialData = 3'h 1, *)
  (*   Get            = 3'h 4 *)
  (* } tl_a_op_e; *)
  Definition tl_a_op_e      := BitVec 3.
  Definition PutFullData    := Constant tl_a_op_e 0.
  Definition PutPartialData := Constant tl_a_op_e 1.
  Definition Get            := Constant tl_a_op_e 4.

  (* typedef enum logic [2:0] { *)
  (*   AccessAck     = 3'h 0, *)
  (*   AccessAckData = 3'h 1 *)
  (* } tl_d_op_e; *)
  Definition tl_d_op_e     := BitVec 3.
  Definition AccessAck     := Constant tl_d_op_e 0.
  Definition AccessAckData := Constant tl_d_op_e 1.

  Definition io_req : type :=
    Bit **          (* read *)
    Bit **          (* write *)
    BitVec TL_AW ** (* address *)
    BitVec TL_DW ** (* write_data *)
    BitVec TL_DBW   (* write_mask *)
    .

  Definition sha_word := BitVec 32.
  Definition sha_block := Vec sha_word 16.
  (* Definition sha_digest := sha_word ** sha_word ** sha_word ** sha_word ** sha_word ** sha_word ** sha_word ** sha_word. *)
  Definition sha_digest := Vec sha_word 8.

  (* Convert TLUL packets to a simple read/write register interface *)
  (* This is similar to OpenTitan's tlul_adapter_reg, but for simplicity we
   * provide all registers for the adapter to read from, rather than providing
   * a readback signal. Providing a same-cycle readback signal like OT version
   * is difficult without delayless loop *)
  Definition tlul_adapter_reg {reg_count}
    : Circuit _ [tl_h2d_t; Vec (BitVec 32) reg_count ] (tl_d2h_t ** io_req) := {{
    fun incoming_tlp registers =>
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

    let/delay '(reqid, reqsz, rspop, error, outstanding, we_o; re_o) :=

      let a_ack := a_valid && !outstanding in
      let d_ack := outstanding && d_ready in

      let rd_req := a_ack && a_opcode == `Get` in
      let wr_req := a_ack &&
        (a_opcode == `PutFullData` || a_opcode == `PutPartialData`) in

      (* TODO(blaxill): skipping malformed tl packet detection *)
      let err_internal := `Zero` in
      let error_i := `Zero` in

      let '(reqid, reqsz, rspop, error; outstanding) :=
        if a_ack then
          ( a_source
          , a_size
          , if rd_req then `AccessAckData` else `AccessAck`
          , error_i || err_internal
          , `One`
          )
        else
          (reqid, reqsz, rspop, error, if d_ack then `Zero` else outstanding)
      in

      let we_o := wr_req && !err_internal in
      let re_o := rd_req && !err_internal in

      (reqid, reqsz, rspop, error, outstanding, we_o, re_o)
      initially (0,(0,(0,(false,(false,(false,false))))))
        : denote_type (BitVec _ ** BitVec _ ** BitVec _ ** Bit ** Bit ** Bit ** Bit)
    in

    let wdata_o := a_data in
    let be_o    := a_mask in

    ( ( outstanding
      , rspop
      , `K 0`
      , reqsz
      , reqid
      , `K 0`
      , `index` registers (`bvslice 2 30` a_address)
      , `K 0`
      , error
      , !outstanding
      )
    , (re_o, we_o, a_address, a_data, a_mask)
    )

  }}.

End Var.

Definition tl_h2d := denote_type tl_h2d_t.
Definition tl_h2d_default := default (t := tl_h2d_t).

Ltac destruct_tl_h2d_step :=
  let t1 := eval unfold tl_h2d in tl_h2d in
  let t2 := eval simpl in t1 in
  match goal with
  | v : tl_h2d |- _ => unfold tl_h2d in v
  | v : t1 |- _ => simpl in v
  | v : t2 |- _ =>
    destruct v as (?a_valid, (?a_opcode, (?a_param, (?a_size, (?a_source,
                  (?a_address, (?a_mask, (?a_data, (?a_user, ?d_ready)))))))))
  end.
Ltac destruct_tl_h2d := repeat destruct_tl_h2d_step.

Definition a_valid   : tl_h2d -> bool := ltac:(intros; destruct_tl_h2d; apply a_valid).
Definition a_opcode  : tl_h2d -> N := ltac:(intros; destruct_tl_h2d; apply a_opcode).
Definition a_param   : tl_h2d -> N := ltac:(intros; destruct_tl_h2d; apply a_param).
Definition a_size    : tl_h2d -> N := ltac:(intros; destruct_tl_h2d; apply a_size).
Definition a_source  : tl_h2d -> N := ltac:(intros; destruct_tl_h2d; apply a_source).
Definition a_address : tl_h2d -> N := ltac:(intros; destruct_tl_h2d; apply a_address).
Definition a_mask    : tl_h2d -> N := ltac:(intros; destruct_tl_h2d; apply a_mask).
Definition a_data    : tl_h2d -> N := ltac:(intros; destruct_tl_h2d; apply a_data).
Definition a_user    : tl_h2d -> N := ltac:(intros; destruct_tl_h2d; apply a_user).
Definition d_ready   : tl_h2d -> bool := ltac:(intros; destruct_tl_h2d; apply d_ready).

Definition mk_tl_h2d (a_valid : bool) (a_opcode : N) (a_param : N) (a_size : N)
           (a_source : N) (a_address : N) (a_mask : N) (a_data : N) (a_user : N)
           (d_ready : bool) : tl_h2d :=
  (a_valid, (a_opcode, (a_param, (a_size, (a_source, (a_address, (a_mask, (a_data, (a_user, d_ready))))))))).

Ltac tl_h2d_setter v h2d x :=
  unfold tl_h2d in h2d; simpl in h2d;
  destruct h2d as (a_valid', (a_opcode', (a_param', (a_size', (a_source',
                  (a_address', (a_mask', (a_data', (a_user', d_ready')))))))));
  let setter :=
      (match eval pattern x in (mk_tl_h2d a_valid' a_opcode' a_param' a_size'
                                          a_source' a_address' a_mask' a_data'
                                          a_user' d_ready') with
       | ?set_x _ => constr:(set_x v)
       end) in
  exact setter.

Definition set_a_valid   : bool -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_valid').
Definition set_a_opcode  : N -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_opcode').
Definition set_a_param   : N -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_param').
Definition set_a_size    : N -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_size').
Definition set_a_source  : N -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_source').
Definition set_a_address : N -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_address').
Definition set_a_mask    : N -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_mask').
Definition set_a_data    : N -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_data').
Definition set_a_user    : N -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d a_user').
Definition set_d_ready   : bool -> tl_h2d -> tl_h2d := ltac:(intros v h2d; tl_h2d_setter v h2d d_ready').

Definition tl_d2h := denote_type tl_d2h_t.
Definition tl_d2h_default := default (t := tl_d2h_t).

Ltac destruct_tl_d2h_step :=
  let t1 := eval unfold tl_d2h in tl_d2h in
  let t2 := eval simpl in t1 in
  match goal with
  | v : tl_d2h |- _ => unfold tl_d2h in v
  | v : t1 |- _ => simpl in v
  | v : t2 |- _ =>
    destruct v as (?d_valid, (?d_opcode, (?d_param, (?d_size, (?d_source,
                  (?d_sink, (?d_data, (?d_user, (?d_error, ?a_ready)))))))))
  end.

Ltac destruct_tl_d2h := repeat destruct_tl_d2h_step.

Definition d_valid  : tl_d2h -> bool := ltac:(intros; destruct_tl_d2h; apply d_valid).
Definition d_opcode : tl_d2h -> N := ltac:(intros; destruct_tl_d2h; apply d_opcode).
Definition d_param  : tl_d2h -> N := ltac:(intros; destruct_tl_d2h; apply d_param).
Definition d_size   : tl_d2h -> N := ltac:(intros; destruct_tl_d2h; apply d_size).
Definition d_source : tl_d2h -> N := ltac:(intros; destruct_tl_d2h; apply d_source).
Definition d_sink   : tl_d2h -> N := ltac:(intros; destruct_tl_d2h; apply d_sink).
Definition d_data   : tl_d2h -> N := ltac:(intros; destruct_tl_d2h; apply d_data).
Definition d_user   : tl_d2h -> N := ltac:(intros; destruct_tl_d2h; apply d_user).
Definition d_error  : tl_d2h -> bool := ltac:(intros; destruct_tl_d2h; apply d_error).
Definition a_ready  : tl_d2h -> bool := ltac:(intros; destruct_tl_d2h; apply a_ready).

Definition mk_tl_d2h (d_valid : bool) (d_opcode : N) (d_param : N) (d_size : N)
           (d_source : N) (d_sink : N) (d_data : N) (d_user : N) (d_error : bool)
           (a_ready : bool) : tl_d2h :=
  (d_valid, (d_opcode, (d_param, (d_size, (d_source, (d_sink, (d_data, (d_user, (d_error, a_ready))))))))).

Ltac tl_d2h_setter v d2h x :=
  unfold tl_d2h in d2h; simpl in d2h;
  destruct d2h as (d_valid', (d_opcode', (d_param', (d_size', (d_source',
                  (d_sink', (d_data', (d_user', (d_error', a_ready')))))))));
  let setter :=
      (match eval pattern x in (mk_tl_d2h d_valid' d_opcode' d_param' d_size'
                                          d_source' d_sink' d_data' d_user'
                                          d_error' a_ready') with
       | ?set_x _ => constr:(set_x v)
       end) in
  exact setter.

Definition set_d_valid  : bool -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_valid').
Definition set_d_opcode : N -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_opcode').
Definition set_d_param  : N -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_param').
Definition set_d_size   : N -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_size').
Definition set_d_source : N -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_source').
Definition set_d_sink   : N -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_sink').
Definition set_d_data   : N -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_data').
Definition set_d_user   : N -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_user').
Definition set_d_error  : bool -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h d_error').
Definition set_a_ready  : bool -> tl_d2h -> tl_d2h := ltac:(intros v d2h; tl_d2h_setter v d2h a_ready').

Ltac tlsimpl :=
  unfold tl_h2d_default, tl_d2h_default in *; simpl Types.default in *;
  cbn [mk_tl_h2d
         set_a_valid set_a_opcode set_a_param set_a_size set_a_source
         set_a_address set_a_mask set_a_data set_a_user set_d_ready
         a_valid a_opcode a_param a_size a_source a_address a_mask a_data a_user d_ready
         mk_tl_d2h
         set_d_valid set_d_opcode set_d_param set_d_size set_d_source
         set_d_sink set_d_data set_d_user set_d_error set_a_ready
         d_valid d_opcode d_param d_size d_source d_sink d_data d_user d_error a_ready] in *;
  unfold mk_tl_h2d, mk_tl_d2h in *.
