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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Datatypes.Prod.

Require Import Cava.Util.Byte.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.
Require Import Cava.TLUL.
Require Import Cava.Invariant.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.List.
Require Import Cava.Util.If.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Byte.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Word.LittleEndianList.
Require Import HmacHardware.Hmac.
Require Import HmacHardware.Sha256.
Require HmacSoftware.HmacSemantics.

Import ListNotations.

Axiom hmac_repr: Type.
(* Note: hmac_repr might/should be an Inductive, so probably no hmac_repr_msg getter will
   exists, but we will need to do a match, and assert False in the other cases *)
Axiom hmac_repr_msg: hmac_repr -> list Byte.byte.
Axiom hmac_repr_max_cycles_until_done: hmac_repr -> nat.

Instance hmac_invariant: invariant_for hmac hmac_repr. Admitted.

(* TLUL communication state *)
Inductive tlul_protocol_state :=
(* host is not interested in talking to device at the moment *)
| HostNotInterested
(* host wants to talk to device and is waiting for device to become ready *)
| HostWaitingForReady(maxDelay: nat)
(* host can and will send a packet in the next cycle *)
| HostCanSend
(* host sent a message to device and is waiting for a reply from device *)
| HostWaitingForReply(packet: tl_h2d)(maxDelay: nat).

Definition tlul_state_step(s1 s2: tlul_protocol_state): Prop :=
  match s1 with
  | HostNotInterested =>
    s2 = HostNotInterested \/
    exists maxDelay, s2 = HostWaitingForReady maxDelay
  | HostWaitingForReady maxDelay =>
    (exists maxDelay', maxDelay = S maxDelay' /\ s2 = HostWaitingForReady maxDelay') \/
    s2 = HostCanSend
  | HostCanSend => exists packet maxDelay, s2 = HostWaitingForReply packet maxDelay
  | HostWaitingForReply packet maxDelay =>
    (exists maxDelay', maxDelay = S maxDelay' /\ s2 = HostWaitingForReply packet maxDelay') \/
    s2 = HostNotInterested
  end.

Definition a_valid_of_current_tlul_state(s: tlul_protocol_state): bool :=
  match s with
  | HostNotInterested => false
  | HostWaitingForReady maxDelay => false
  | HostCanSend => true
  | HostWaitingForReply packet maxDelay => false
  end.

Definition d_ready_of_current_tlul_state(s: tlul_protocol_state): bool :=
  match s with
  | HostNotInterested => false
  | HostWaitingForReady maxDelay => false
  | HostCanSend => true
  | HostWaitingForReply packet maxDelay => true
  end.

Definition d_valid_of_current_and_next_tlul_state(s1 s2: tlul_protocol_state): bool :=
  match s1 with
  | HostWaitingForReply packet maxDelay =>
    match s2 with
    | HostWaitingForReply packet' maxDelay' => false
    | _ => true
    end
  | _ => false
  end.

(* If the host and device both behave correctly, then each device cycle that takes in
   h2d and outputs d2h (ie `step circuit circuit_state1 h2d = (circuit_state2, d2h)`)
   corresponds to a transition in the following transition system: *)
Definition tlul_step(s1: tlul_protocol_state)(h2d: tl_h2d)
                    (s2: tlul_protocol_state)(d2h: tl_d2h): Prop :=
  a_valid h2d = a_valid_of_current_tlul_state s1 /\
  d_ready h2d = d_ready_of_current_tlul_state s1 /\
  d_valid d2h = d_valid_of_current_and_next_tlul_state s1 s2 /\
  match s1 with
  | HostNotInterested =>
    match s2 with
    | HostNotInterested => True
    | HostWaitingForReady maxDelay => a_ready d2h = false
    | HostCanSend => a_ready d2h = true
    | HostWaitingForReply packet maxDelay => False
    end
  | HostWaitingForReady maxDelay =>
    match s2 with
    | HostNotInterested => False
    | HostWaitingForReady maxDelay' => a_ready d2h = false /\ maxDelay = S maxDelay'
    | HostCanSend => a_ready d2h = true
    | HostWaitingForReply packet maxDelay => False
    end
  | HostCanSend =>
    match s2 with
    | HostWaitingForReply packet maxDelay => packet = h2d
    | _ => False
    end
  | HostWaitingForReply packet maxDelay =>
    match s2 with
    | HostNotInterested => True
    | HostWaitingForReady maxDelay' => a_ready d2h = false
    | HostCanSend => a_ready d2h = true
    | HostWaitingForReply packet' maxDelay' => packet' = packet /\ maxDelay = S maxDelay'
    end
  end.

Section WithParams.
  Context {word: word 32} {word_ok: word.ok word}.

  Definition REG_DIGEST_0: nat.
    let r := eval unfold HmacHardware.Hmac.REG_DIGEST_0 in HmacHardware.Hmac.REG_DIGEST_0 in
    lazymatch r with
    | Constant _ ?v => exact (N.to_nat v)
    end.
  Defined.

  Definition REG_CFG: nat.
    let r := eval unfold HmacHardware.Hmac.REG_CFG in HmacHardware.Hmac.REG_CFG in
    lazymatch r with
    | Constant _ ?v => exact (N.to_nat v)
    end.
  Defined.

  Definition REG_INTR_STATE: nat := 0.
  Definition REG_INTR_ENABLE: nat := 1.

  Definition N_le_word_list_to_byte_list: list N -> list Byte.byte :=
    List.flat_map (fun n => le_split 4 (Z.of_N n)).

  Definition get_hl_config(regs: list N): HmacSemantics.idle_data := {|
    HmacSemantics.intr_enable := word.of_Z (Z.of_N (List.nth REG_INTR_ENABLE regs 0%N));
    HmacSemantics.hmac_done := N.testbit 0 (List.nth REG_INTR_ENABLE regs 0%N);
    HmacSemantics.hmac_en := N.testbit 0 (List.nth REG_CFG regs 0%N);
    HmacSemantics.sha_en := N.testbit 1 (List.nth REG_CFG regs 0%N);
    HmacSemantics.swap_endian := N.testbit 2 (List.nth REG_CFG regs 0%N);
    HmacSemantics.swap_digest := N.testbit 3 (List.nth REG_CFG regs 0%N);
  |}.

  Instance hmac_top_invariant: invariant_for hmac_top HmacSemantics.state :=
    fun (circuit_state: denote_type hmac_top_state) (stm_state: HmacSemantics.state) =>
      let '((wasfull, (d2h, regs)), (tlul_st, hmac_st)) := circuit_state in
      exists hmac_r: hmac_repr, hmac_invariant hmac_st hmac_r /\
      match stm_state with
      | HmacSemantics.IDLE digest config =>
        digest = N_le_word_list_to_byte_list (List.firstn 8 (List.skipn REG_DIGEST_0 regs)) /\
        config = get_hl_config regs
      | HmacSemantics.CONSUMING buf =>
        get_hl_config regs = HmacSemantics.sha_default_cfg /\
        hmac_repr_msg hmac_r = buf
      | HmacSemantics.PROCESSING buf ncycles =>
        get_hl_config regs = HmacSemantics.sha_default_cfg /\
        hmac_repr_msg hmac_r = buf /\
        Z.of_nat (hmac_repr_max_cycles_until_done hmac_r) = ncycles
      end.

  Instance hmac_top_specification: specification_for hmac_top HmacSemantics.state := {|
    reset_repr := HmacSemantics.IDLE (List.repeat Byte.x00 32) HmacSemantics.zero_cfg;
    precondition h2d st := True;
    update_repr h2d st :=
      match st with
      | HmacSemantics.IDLE digest config => st
      | HmacSemantics.CONSUMING buf => st
      | HmacSemantics.PROCESSING buf ncycles => st
      end;
    postcondition h2d st d2h := True;
  |}.

  Lemma hmac_top_invariant_at_reset: invariant_at_reset hmac_top.
  Admitted.

  Lemma hmac_top_invariant_preserved: invariant_preserved hmac_top.
  Proof.
    simplify_invariant hmac_top. cbn [absorb_any].
    simplify_spec hmac_top.
    intros input state repr new_repr.
  Admitted.

  Lemma hmac_top_output_correct: output_correct hmac_top.
  Proof.
    simplify_invariant hmac_top. simplify_spec hmac_top.
    intros input state repr new_repr.
  Admitted.

End WithParams.
