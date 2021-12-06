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

Import ListNotations.

Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Invariant.
Require Import Cava.Primitives.
Require Import Cava.Types.
Require Import Cava.Util.Tactics.

Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.Tactics.

Require Import ExtLib.Data.List.
Require Import ExtLib.Structures.Monoid.

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
  Import PrimitiveNotations.

  Context {var : tvar}.

  Local Open Scope N.

  (* typedef enum logic [2:0] { *)
  (*   PutFullData    = 3'h 0, *)
  (*   PutPartialData = 3'h 1, *)
  (*   Get            = 3'h 4 *)
  (* } tl_a_op_e; *)
  Definition PutFullData    := 0.
  Definition PutPartialData := 1.
  Definition Get            := 4.

  (* typedef enum logic [2:0] { *)
  (*   AccessAck     = 3'h 0, *)
  (*   AccessAckData = 3'h 1 *)
  (* } tl_d_op_e; *)
  Definition AccessAck     := 0.
  Definition AccessAckData := 1.

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

  Definition tlul_adapter_state :=
    (BitVec TL_AIW ** BitVec TL_SZW ** BitVec 3 ** BitVec 32 ** Bit ** Bit ** Bit ** Bit)%circuit_type.

  (* Convert TLUL packets to a simple read/write register interface *)
  (* This is similar to OpenTitan's tlul_adapter_reg, but for simplicity we
   * provide all registers for the adapter to read from, rather than providing
   * a readback signal. Providing a same-cycle readback signal like OT version
   * is difficult without delayless loop *)
  Definition tlul_adapter_reg {reg_count}
    : Circuit tlul_adapter_state [tl_h2d_t; Vec (BitVec 32) reg_count ] (tl_d2h_t ** io_req) := {{
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

    let/delay '(reqid, reqsz, rspop, reqaddress, error, outstanding,
                (* output only signals: *)
                we_o; re_o) :=

      let a_ack := a_valid && !outstanding in
      let d_ack := outstanding && d_ready in

      let rd_req := a_ack && a_opcode == `K Get` in
      let wr_req := a_ack &&
        (a_opcode == `K PutFullData` || a_opcode == `K PutPartialData`) in

      (* TODO(blaxill): skipping malformed tl packet detection *)
      let err_internal := `Zero` in
      let error_i := `Zero` in

      let '(reqid, reqsz, rspop, reqaddress, error; outstanding) :=
          if a_ack then
            ( a_source
              , a_size
              , if rd_req then `K AccessAckData` else `K AccessAck`
              , a_address
              , error_i || err_internal
              , `One`
            )
          else
            (reqid, reqsz, rspop, reqaddress, error, if d_ack then `Zero` else outstanding)
      in

      let we_o := wr_req && !err_internal in
      let re_o := rd_req && !err_internal in

      (reqid, reqsz, rspop, reqaddress, error, outstanding, we_o, re_o)
      initially default
        : denote_type (BitVec _ ** BitVec _ ** BitVec _ ** BitVec _ ** Bit ** Bit ** Bit ** Bit)
    in

    let wdata_o := a_data in
    let be_o    := a_mask in

    ( ( outstanding
      , rspop
      , `K 0`
      , reqsz
      , reqid
      , `K 0`
      , `index` registers (`bvslice 2 30` reqaddress)
      , `K 0`
      , error
      , !outstanding
      )
    , (re_o, we_o, a_address, a_data, a_mask)
    )

  }}.
End Var.

Ltac destruct_tlul_adapter_reg_state reg_count :=
  destruct_state (tlul_adapter_reg (var:=denote_type) (reg_count:=reg_count))
                 ipattern:((?reqid, (?reqsz, (?rspop, (?reqaddress, (?error, (?outstanding, (?we_o, ?re_o)))))))).

Section StateGetters.
  Definition var : tvar := denote_type.
  Context {reg_count : nat}.

  Definition tlul_adapter_reg_state_reqid (s : denote_type (state_of (tlul_adapter_reg (reg_count:=reg_count))))
    : N := ltac:(destruct_tlul_adapter_reg_state reg_count; apply reqid).
  Definition tlul_adapter_reg_state_reqsz (s : denote_type (state_of (tlul_adapter_reg (reg_count:=reg_count))))
    : N := ltac:(destruct_tlul_adapter_reg_state reg_count; apply reqsz).
  Definition tlul_adapter_reg_state_rspop (s : denote_type (state_of (tlul_adapter_reg (reg_count:=reg_count))))
    : N := ltac:(destruct_tlul_adapter_reg_state reg_count; apply rspop).
  Definition tlul_adapter_reg_state_reqaddress (s : denote_type (state_of (tlul_adapter_reg (reg_count:=reg_count))))
    : N := ltac:(destruct_tlul_adapter_reg_state reg_count; apply reqaddress).

  Definition tlul_adapter_reg_state_error (s : denote_type (state_of (tlul_adapter_reg (reg_count:=reg_count))))
    : bool := ltac:(destruct_tlul_adapter_reg_state reg_count; apply error).
  Definition tlul_adapter_reg_state_outstanding (s : denote_type (state_of (tlul_adapter_reg (reg_count:=reg_count))))
    : bool := ltac:(destruct_tlul_adapter_reg_state reg_count; apply outstanding).
  Definition tlul_adapter_reg_state_we_o (s : denote_type (state_of (tlul_adapter_reg (reg_count:=reg_count))))
    : bool := ltac:(destruct_tlul_adapter_reg_state reg_count; apply we_o).
  Definition tlul_adapter_reg_state_re_o (s : denote_type (state_of (tlul_adapter_reg (reg_count:=reg_count))))
    : bool := ltac:(destruct_tlul_adapter_reg_state reg_count; apply re_o).
End StateGetters.

Ltac tlul_adapter_reg_state_simpl :=
  cbn [tlul_adapter_reg_state_reqid tlul_adapter_reg_state_reqsz
       tlul_adapter_reg_state_rspop tlul_adapter_reg_state_reqaddress
       tlul_adapter_reg_state_error tlul_adapter_reg_state_outstanding
       tlul_adapter_reg_state_we_o tlul_adapter_reg_state_re_o] in *.

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

Definition a_valid   (h2d: tl_h2d) : bool := ltac:(destruct_tl_h2d; apply a_valid).
Definition a_opcode  (h2d: tl_h2d) : N := ltac:(destruct_tl_h2d; apply a_opcode).
Definition a_param   (h2d: tl_h2d) : N := ltac:(destruct_tl_h2d; apply a_param).
Definition a_size    (h2d: tl_h2d) : N := ltac:(destruct_tl_h2d; apply a_size).
Definition a_source  (h2d: tl_h2d) : N := ltac:(destruct_tl_h2d; apply a_source).
Definition a_address (h2d: tl_h2d) : N := ltac:(destruct_tl_h2d; apply a_address).
Definition a_mask    (h2d: tl_h2d) : N := ltac:(destruct_tl_h2d; apply a_mask).
Definition a_data    (h2d: tl_h2d) : N := ltac:(destruct_tl_h2d; apply a_data).
Definition a_user    (h2d: tl_h2d) : N := ltac:(destruct_tl_h2d; apply a_user).
Definition d_ready   (h2d: tl_h2d) : bool := ltac:(destruct_tl_h2d; apply d_ready).

Ltac tl_h2d_setter v h2d x :=
  unfold tl_h2d in h2d; simpl in h2d;
  destruct h2d as (a_valid', (a_opcode', (a_param', (a_size', (a_source',
                  (a_address', (a_mask', (a_data', (a_user', d_ready')))))))));
  let setter :=
      (match eval pattern x in (a_valid', (a_opcode', (a_param', (a_size', (a_source',
                  (a_address', (a_mask', (a_data', (a_user', d_ready'))))))))) with
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

Definition d_valid  (d2h : tl_d2h) : bool := ltac:(destruct_tl_d2h; apply d_valid).
Definition d_opcode (d2h : tl_d2h) : N := ltac:(destruct_tl_d2h; apply d_opcode).
Definition d_param  (d2h : tl_d2h) : N := ltac:(destruct_tl_d2h; apply d_param).
Definition d_size   (d2h : tl_d2h) : N := ltac:(destruct_tl_d2h; apply d_size).
Definition d_source (d2h : tl_d2h) : N := ltac:(destruct_tl_d2h; apply d_source).
Definition d_sink   (d2h : tl_d2h) : N := ltac:(destruct_tl_d2h; apply d_sink).
Definition d_data   (d2h : tl_d2h) : N := ltac:(destruct_tl_d2h; apply d_data).
Definition d_user   (d2h : tl_d2h) : N := ltac:(destruct_tl_d2h; apply d_user).
Definition d_error  (d2h : tl_d2h) : bool := ltac:(destruct_tl_d2h; apply d_error).
Definition a_ready  (d2h : tl_d2h) : bool := ltac:(destruct_tl_d2h; apply a_ready).

Ltac tl_d2h_setter v d2h x :=
  unfold tl_d2h in d2h; simpl in d2h;
  destruct d2h as (d_valid', (d_opcode', (d_param', (d_size', (d_source',
                  (d_sink', (d_data', (d_user', (d_error', a_ready')))))))));
  let setter :=
      (match eval pattern x in (d_valid', (d_opcode', (d_param', (d_size', (d_source',
                               (d_sink', (d_data', (d_user', (d_error', a_ready'))))))))) with
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
  cbn [set_a_valid set_a_opcode set_a_param set_a_size set_a_source
       set_a_address set_a_mask set_a_data set_a_user set_d_ready
       a_valid a_opcode a_param a_size a_source a_address a_mask a_data a_user d_ready
       set_d_valid set_d_opcode set_d_param set_d_size set_d_source
       set_d_sink set_d_data set_d_user set_d_error set_a_ready
       d_valid d_opcode d_param d_size d_source d_sink d_data d_user d_error a_ready] in *.

Section TLSpec.
  Local Open Scope N_scope.

  Context {reg_count : nat}.

  Variant repr_state :=
  | Idle
  | OutstandingAccessAckData (h2d : tl_h2d) (regs : list N)
  | OutstandingAccessAck (h2d : tl_h2d).

  Definition update_repr_state (input : denote_type (input_of (tlul_adapter_reg (reg_count:=reg_count)))) repr :=
    let '(h2d, (regs, tt)) := input in
    match repr with
    | Idle =>
      if a_valid h2d then
        if a_opcode h2d =? Get then
          OutstandingAccessAckData h2d regs
        else if a_opcode h2d =? PutFullData then
               OutstandingAccessAck h2d
             else (* unreachable *) repr
      else
        repr
    | _ =>
      if d_ready h2d then Idle
      else match repr with
           | OutstandingAccessAckData h2d _ => OutstandingAccessAckData h2d regs
           | _ => repr
           end
    end.

  Instance tl_specification
    : specification_for (tlul_adapter_reg (reg_count:=reg_count)) repr_state :=
    {| reset_repr := Idle;

       update_repr := update_repr_state;

       precondition :=
         fun (input : denote_type (input_of tlul_adapter_reg))
           (repr : repr_state) =>
           let '(h2d, (regs, tt)) := input in
           reg_count = length regs
           /\ (a_valid h2d = true
              -> (a_opcode h2d = Get \/ a_opcode h2d = PutFullData));

       postcondition :=
         fun (input : denote_type (input_of (tlul_adapter_reg (reg_count:=reg_count))))
           (repr : repr_state)
           (output : denote_type (output_of (tlul_adapter_reg (reg_count:=reg_count)))) =>
           exists h2d regs repr' d2h io_re io_we io_address io_data io_mask,
               input = (h2d, (regs, tt))
               /\ output = (d2h, (io_re, (io_we, (io_address, (io_data, io_mask)))))
               /\ repr' = update_repr_state input repr
               /\ match repr' with
                 | Idle =>
                   d_valid    d2h = false
                   /\ d_param  d2h = 0
                   /\ d_sink   d2h = 0
                   /\ d_user   d2h = 0
                   /\ d_error  d2h = false
                   /\ a_ready  d2h = true
                   /\ io_re = false
                   /\ io_we = false

                 | OutstandingAccessAckData h2d regs =>
                     d_valid    d2h = true
                     /\ d_opcode d2h = AccessAckData
                     /\ d_param  d2h = 0
                     /\ d_size   d2h = (a_size h2d)
                     /\ d_source d2h = (a_source h2d)
                     /\ d_sink   d2h = 0
                     /\ d_data   d2h = (List.nth (N.to_nat ((((a_address h2d) / 4) mod (2 ^ 30)))) regs 0%N)
                     /\ d_user   d2h = 0
                     /\ d_error  d2h = false
                     /\ a_ready  d2h = false
                     /\ match repr with
                       | Idle => if a_valid h2d then
                                  io_re = true
                                  /\ io_address = a_address h2d
                                else io_re = false
                       | _ => io_re = false
                       end
                     /\ io_we = false

                 | OutstandingAccessAck h2d  =>
                          d_valid    d2h = true
                          /\ d_opcode d2h = AccessAck
                          /\ d_param  d2h = 0
                          (* /\ d_size   d2h =  *)
                          /\ d_source d2h = (a_source h2d)
                          /\ d_sink   d2h = 0
                          /\ d_user   d2h = 0
                          /\ d_error  d2h = false
                          /\ a_ready  d2h = false
                          /\ io_re = false
                          /\ match repr with
                            | Idle => if a_valid h2d then
                                       io_we = true
                                       /\ io_address = a_address h2d
                                       /\ io_data = a_data h2d
                                       /\ io_mask = a_mask h2d
                                     else io_we = false
                            | _ => io_we = false
                            end
                 end;
    |}.

  Global Instance tlul_invariant : invariant_for (tlul_adapter_reg (reg_count:=reg_count)) repr_state :=
    fun (state : denote_type (state_of tlul_adapter_reg)) repr =>
      tlul_adapter_reg_state_error state = false
      /\ match repr with
        | Idle =>
          tlul_adapter_reg_state_outstanding (reg_count:=reg_count) state = false
        | OutstandingAccessAckData h2d regs =>
          tlul_adapter_reg_state_outstanding state = true
          /\ tlul_adapter_reg_state_reqid state = (a_source h2d)
          /\ tlul_adapter_reg_state_reqsz state = (a_size h2d)
          /\ tlul_adapter_reg_state_rspop state = AccessAckData
          /\ tlul_adapter_reg_state_reqaddress state = (a_address h2d)
          /\ reg_count = length regs
          /\ a_opcode h2d = Get
        | OutstandingAccessAck h2d =>
          tlul_adapter_reg_state_outstanding state = true
          /\ tlul_adapter_reg_state_reqid state = (a_source h2d)
          /\ tlul_adapter_reg_state_rspop state = AccessAck
          /\ a_opcode h2d = PutFullData
        end.

    Lemma tlul_adapter_reg_invariant_at_reset : invariant_at_reset tlul_adapter_reg.
    Proof.
      simplify_invariant (tlul_adapter_reg (reg_count:=reg_count)).
      cbn. auto.
    Qed.

    Local Hint Unfold tlul_adapter_state : stepsimpl.

    Lemma tlul_adapter_reg_invariant_preserved : invariant_preserved tlul_adapter_reg.
    Proof.
      intros (h2d & regs & t) state repr. destruct t.
      cbn in state. destruct_tlul_adapter_reg_state reg_count.
      destruct_tl_h2d.
      intros; subst.
      simplify_invariant (tlul_adapter_reg (reg_count:=reg_count)).
      simplify_spec (tlul_adapter_reg (reg_count:=reg_count)).
      cbv [tlul_adapter_reg]. stepsimpl.
      tlul_adapter_reg_state_simpl. tlsimpl.
      logical_simplify.
      repeat (destruct_pair_let; cbn [fst snd]).
      tlul_adapter_reg_state_simpl.
      subst.
      ssplit.
      - destruct (a_valid0 && negb outstanding)%bool; reflexivity.
      - unfold update_repr_state.
        destruct repr; [destruct a_valid0 | destruct d_ready0 ..];
          tlsimpl; boolsimpl.
        2-6: logical_simplify; subst outstanding; boolsimpl; ssplit; try reflexivity; assumption.
        destruct H1; [reflexivity|..]; subst outstanding a_opcode0; cbn; [|auto].
        ssplit; try reflexivity; assumption.
    Qed.

    Lemma tlul_adapter_reg_output_correct : output_correct tlul_adapter_reg.
    Proof.
      intros (h2d, (regs, t)) state repr. destruct t.
      cbn in state. destruct_tlul_adapter_reg_state reg_count.
      destruct_tl_h2d.
      intros.
      simplify_invariant (tlul_adapter_reg (reg_count:=reg_count)).
      logical_simplify; subst.
      simplify_spec (tlul_adapter_reg (reg_count:=reg_count)).
      cbv [tlul_adapter_reg]. stepsimpl. logical_simplify.
      tlul_adapter_reg_state_simpl. tlsimpl.
      (* match goal with *)
      (* | h : reg_count = _ |- _ => clear h *)
      (* end. *)
      subst.
      repeat (destruct_pair_let; cbn [fst snd]).
      destruct repr; destruct a_valid0; destruct d_ready0;
        tlsimpl; boolsimpl; subst.
      all: try match goal with
               | H: true = true -> _ |- _ =>
                 destruct H; [auto|subst..]
               end.
      all: logical_simplify; subst; boolsimpl.
      all: repeat eexists; cbn.
      all: rewrite List.resize_noop by assumption.
      all: change 1073741823 with (N.ones 30);
        rewrite N.land_ones;
        replace 4 with (2 ^ 2) by reflexivity;
        rewrite <- ! N.shiftr_div_pow2;
        try reflexivity.
    Qed.

    Existing Instances tlul_adapter_reg_invariant_at_reset tlul_adapter_reg_invariant_preserved
             tlul_adapter_reg_output_correct.
    Global Instance tlul_adapter_reg_correctness : correctness_for tlul_adapter_reg.
    Proof. constructor; typeclasses eauto. Defined.
End TLSpec.
