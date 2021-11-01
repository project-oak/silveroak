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

Require Import HmacHardware.Hmac.
Require Import HmacHardware.Sha256.
Require Import HmacHardware.Sha256InnerProperties.
Require Import HmacHardware.Sha256PadderProperties.
Require Import HmacHardware.Sha256Properties.
Require Import HmacSpec.SHA256Properties.

Import ListNotations.

Local Notation ShaRepr :=
  (list Byte.byte * bool * nat * nat * nat * bool)%type.
Local Notation FifoRepr :=
  (list N * list Byte.byte * bool * list Byte.byte)%type.

Local Notation HmacInnerSpecRepr :=
  ( nat
  * bool
  * bool
  * bool
  * bool
  * option (list N)
  * bool
  * ShaRepr
  )%type.

Instance hmac_inner_invariant : invariant_for hmac_inner HmacInnerSpecRepr :=
  fun circuit_state '(state, input_done, raised_process, sha_signaled_done, sha_ready, digest_buf, has_content, sha_repr) =>
  let
    '( (finishing, (waiting_for_digest, (accept_fifo, (ptr, (inner_state, (digest, circ_sha_ready))))))
    , circuit_sha_state) := circuit_state in

  let '((ready, (block, (digest1, (count, done)))),
        (sha256_padder_state, sha256_inner_state)) := circuit_sha_state in

  let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := sha_repr in

     sha256_invariant circuit_sha_state sha_repr
  /\ (state = 0 \/ state = 2 \/ state = 3)
  /\ (inner_state = N.of_nat state)
  /\ (if state =? 3 then input_done = true else True)
  /\ (if msg_complete then input_done = true else True)

  /\ sha_ready = circ_sha_ready
  /\ (if state =? 3 then sha_signaled_done = negb waiting_for_digest else True )
  /\ (if state =? 0 then True else if has_content then cleared = false /\ msg <> [] else True)
  /\ (if state =? 3 then has_content = true else True )
  /\ (if state =? 3 then msg <> [] else True )
  /\ (if state =? 3 then
    (match digest_buf with
    | Some x =>
        x = BigEndianBytes.bytes_to_Ns 4 (SHA256.sha256 msg)
        /\ waiting_for_digest = false
        /\ digest = x
    | _ => waiting_for_digest = true
     end) else digest_buf = None)
  .

Instance hmac_inner_specification
  : specification_for hmac_inner HmacInnerSpecRepr := {|

  reset_repr := (0, false, false, false, false, None, false, reset_repr);

  precondition
    (input : denote_type (input_of hmac_inner))
    '(state, input_done, raised_process, sha_signaled_done, sha_ready, digest_buf, _, sha_repr) :=
    let
      '(fifo_valid, (fifo_data, (fifo_length, (fifo_final,
        (cmd_hash_start, (cmd_hash_process, (cmd_hmac_enable, (hmac_key_vec, tt)))))))) := input
    in
    let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := sha_repr in

    (* ** SHA256 conditions : ** *)
    (* the total message length (including any new data) cannot exceed 2 ^
       64 bits (2^61 bytes) -- using N so Coq doesn't try to compute 2 ^ 61
       in nat *)
    (N.of_nat (length msg) + (if fifo_final then fifo_length else 4) < 2 ^ 61)%N
     (* ...and if data is valid, it must be in expected range *)
     /\ (if fifo_valid
        then if fifo_final
             then (fifo_data < 2 ^ (8 * fifo_length))%N
                  /\ (1 <= fifo_length <= 4)%N
             else (fifo_data < 2 ^ 32)%N
        else True)

    /\ (if fifo_final then fifo_valid = true else True)
    (* Disable cmd_hmac_enable mode for this spec by only allowing
    cmd_hmac_enable flag during idle moments *)
    /\ (if cmd_hmac_enable then (state = 0 /\ cmd_hash_start <> true) else True)
    /\ (if cmd_hash_process then (state = 2 \/ state = 3) else raised_process = false)
    /\ (if state =? 0 then fifo_valid = false else cmd_hash_start = true)
    /\ (if cmd_hash_start then True else fifo_valid = false)

    (* no valid input after fifo_final *)
    /\ (if input_done then fifo_valid = false else True)

    (* cmd_hash_process must be continuously asserted *)
    /\ (if raised_process then cmd_hash_process  = true else True);

  update_repr (input : denote_type (input_of hmac_inner))
    '(state, input_done, raised_process, sha_signaled_done, sha_ready, digest_buf, has_content, sha_repr) :=

    let
      '(fifo_valid, (fifo_data, (fifo_length, (fifo_final,
        (cmd_hash_start, (cmd_hash_process, (cmd_hmac_enable, (hmac_key_vec, tt)))))))) := input
    in

    let fifo_valid := if sha_ready then fifo_valid else false in

    let sha_input :=
      (* Only emulate sha mode *)
      match state with
      | 0 => (false, (0%N, (false, (0%N, (true, tt)))))
      | 2 => (fifo_valid, (fifo_data, (fifo_final, (fifo_length, (false, tt)))))%bool
      | _ => (false, (0%N, (false, (0%N, (false, tt)))))
      end
    in

    let sha_repr' := update_repr (c:=sha256) sha_input sha_repr in
    let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := sha_repr
    in

    let clear := if state =? 0 then true else false in
    let is_cleared := if clear
                      then true
                      else if (cleared:bool)
                           then negb (fst sha_input)
                           else false in

    let count_16_pre :=
        if (if (padder_byte_index =? 64) then t =? 0 else t =? 64)
        then if (padder_byte_index =? inner_byte_index + 64) then true else false else false
    in
    let count_le15_pre :=
        if (padder_byte_index <? 64) then t =? 0 else t =? 64
    in

    let is_cleared_or_done :=
        if is_cleared
        then true
        else if fifo_valid
             then false
             else
               if count_16_pre
               then false
               else
                if (padder_byte_index =? padded_message_size msg) then if (t =? 64) then true else false else false
    in

    let state' :=
      match state with
      | 0 => if cmd_hash_start then 2 else 0
      | 2 => if sha_ready then if cmd_hash_process then if fifo_final then 3 else 2 else 2 else 2
      | 3 => if sha_signaled_done then 0 else 3
      | _ => 0
      end in


    (* new value of [t] *)
    let new_t :=
        if clear
        then 0
        else if cleared
             then 0
             else if (padder_byte_index =? inner_byte_index)
                  then if t =? 64
                       then t
                       else S t
                  else if (padder_byte_index =? inner_byte_index + 64)
                       then 0
                       else t in

    (* ready for new input only if the inner loop is done and the padder is
       not *)
    let is_ready :=
        if is_cleared
        then true
        else
          if count_16_pre then false
          else if count_le15_pre then
            if (if padder_byte_index =? padded_message_size msg
              then fifo_valid
              else if (msg_complete: bool) then true else fifo_valid)
            then padder_byte_index mod 64 <=? 56
            else true
          else if inner_byte_index =? padder_byte_index
            then
              if if (t =? 64)%nat then true else (inner_byte_index =? 0)%nat
              then true
              else (t =? 63)%nat
            else true
    in

    let input_done' :=
      if state =? 0
      then false
      else
        if input_done
        then true
        else if fifo_final then sha_ready else false
    in

    let raised_process' :=
      if state' =? 0
      then false
      else
        if cmd_hash_process
        then true
        else raised_process
    in

    let digest_buf :=
      if state =? 3 then
        if state' =? 0 then None
        else
          if is_cleared_or_done
          then Some (BigEndianBytes.bytes_to_Ns 4 (SHA256.sha256 msg))
          else None
      else None
    in

    let has_content' :=
      if state =? 0 then false
      else
        if has_content then true else fifo_valid
      (* 0 <? length msg *)
    in

    (state', input_done', raised_process', is_cleared_or_done, is_ready, digest_buf,
      has_content',
      sha_repr');

  postcondition
    (input : denote_type (input_of hmac_inner))
    '(state, input_done, raised_process, sha_signaled_done, sha_ready, digest_buf, _, sha_repr)
    (output : denote_type (output_of hmac_inner)) :=
    let
      '(fifo_valid, (fifo_data, (fifo_length, (fifo_final,
        (cmd_hash_start, (cmd_hash_process, (cmd_hmac_enable, (hmac_key_vec, tt)))))))) := input in

        let fifo_data_valid := if sha_ready then fifo_valid else false in
        let clear := state =? 0 in

    let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := sha_repr in
    (* new value of [cleared] *)
    let is_cleared := if clear
                      then true
                      else if cleared
                           then negb fifo_data_valid
                           else false in

    let count_16_pre :=
        if (if (padder_byte_index =? 64) then t =? 0 else t =? 64)
        then if (padder_byte_index =? inner_byte_index + 64) then true else false else false
    in
    let count_le15_pre :=
        if (padder_byte_index <? 64) then t =? 0 else t =? 64
    in

    let is_cleared_or_done :=
        if is_cleared
        then true
        else if fifo_data_valid
             then false
             else
               if count_16_pre
               then false
               else
                if (padder_byte_index =? padded_message_size msg) then if (t =? 64) then true else false else false
    in

    (* new value of [padder_byte_index] *)
    let new_padder_byte_index :=
        if clear
        then 0
        else if cleared
         then 0
         else if (padder_byte_index =? inner_byte_index)
              then if t =? 64
                   then if (padder_byte_index =? padded_message_size msg)
                        then padder_byte_index
                        else if msg_complete
                             then padder_byte_index + 4
                             else if fifo_data_valid
                                  then padder_byte_index + 4
                                  else padder_byte_index
                   else padder_byte_index
              else if (padder_byte_index =? inner_byte_index + 64)
                   then padder_byte_index
                   else if msg_complete
                        then padder_byte_index + 4
                        else if fifo_data_valid
                             then padder_byte_index + 4
                             else padder_byte_index in

    (* new value of [t] *)
    let new_t :=
        if clear
        then 0
        else if cleared
             then 0
             else if (padder_byte_index =? inner_byte_index)
                  then if t =? 64
                       then t
                       else S t
                  else if (padder_byte_index =? inner_byte_index + 64)
                       then 0
                       else t in

    (* ready for new input only if the inner loop is done and the padder is
       not *)
    let is_ready :=
        if is_cleared
        then true
        else
          if count_16_pre then false
          else if count_le15_pre then
            if (if padder_byte_index =? padded_message_size msg
              then fifo_data_valid
              else if msg_complete then true else fifo_data_valid)
            then padder_byte_index mod 64 <=? 56
            else true
          else if inner_byte_index =? padder_byte_index
            then
              if if (t =? 64)%nat then true else (inner_byte_index =? 0)%nat
              then true
              else (t =? 63)%nat
            else true
    in

    let accept_fifo := if state =? 2 then is_ready else false in

    exists done odigest,
      output = (accept_fifo, (done, odigest))
      /\ match digest_buf with
         | Some x => done = true /\ odigest = x
         | _ => done = false
         end
|}.

(* TODO: move me *)
Ltac nat_const X :=
  match X with
  | O => idtac
  | S ?Y => nat_const Y
  | _ => fail
  end.
Ltac destr_nat_match :=
  match goal with
  | |- context [?X =? ?Y] =>
      nat_const X; nat_const Y;
      destr (X =? Y); try lia
  end.
Ltac destr_nat_match_hyp :=
  match goal with
  | _: context [?X =? ?Y] |- _ =>
      nat_const X; nat_const Y;
      destr (X =? Y); try lia
  end.

Ltac fail_if_if_in X :=
  lazymatch X with
  | context [if _ then _ else _] => fail
  | _ => idtac
  end.

Ltac destruct_one_inner_match :=
  match goal with
  | |- context [if ?B then _ else _] => fail_if_if_in B; destr B
  end.

Lemma hmac_inner_invariant_at_reset :
  invariant_at_reset hmac_inner.
Proof.
  simplify_invariant hmac_inner.
  cbn [reset_repr reset_state hmac_inner hmac_inner_specification sha256 sha256_specification default].
  stepsimpl.

  ssplit;
    lazymatch goal with
    | |- sha256_invariant _ _ => apply sha256_invariant_at_reset
    | _ => reflexivity || lia || idtac
    end.
Qed.

Lemma hmac_inner_invariant_preserved :
  invariant_preserved hmac_inner.
Proof.
  simplify_invariant hmac_inner. cbn [absorb_any].
  simplify_spec hmac_inner.

  intros input state repr new_repr.
  pose (input_:=input). pose (state_:=state). pose (repr_:=repr). pose (new_repr_:=new_repr).
  revert dependent repr. revert dependent state. revert dependent input. revert dependent new_repr.

  intros (((((((new_state, new_input_done), new_raised_process), new_sha_signaled_done), new_sha_ready), new_digest), has_content), new_sha_repr).
  intro.
  intros (fifo_valid, (fifo_data, (fifo_length, (fifo_final,
         (cmd_hash_start, (cmd_hash_process, (cmd_hmac_enable, (hmac_key_vec, [])))))))).
  intro.
  intros
      ( (finishing, (waiting_for_digest, (accept_fifo, (ptr, (inner_state, (digest_circ, sha_ready_circ))))))
      , sha_state_circ).
  intro.
  intros (((((((state, input_done), raised_process), sha_signaled_done), sha_ready), digest), new_has_content), sha_repr).
  intro.
  destruct sha_repr as (((((msg,msg_complete),?),?),?),?).
  destruct new_sha_repr as (((((?,?),?),?),?),?).
  destruct sha_state_circ as ((ready, (?, (?, (?, ?)))), (padder, inner)).
  destruct padder as (?, (?, (?, (?, (?, ?))))).
  destruct inner as (?, (?, (?, ?))).
  intros.

  (* for some reason the modulo expands into ugly match statement wihtout this *)
  remember (n mod 64) as n_mod_64.
  logical_simplify. subst.

  cbv [hmac_inner K]. cbn [negb]. stepsimpl.
  repeat (destruct_pair_let; cbn [fst snd]).

  lazymatch goal with
  | H : sha256_invariant ?state ?repr
    |- context [step sha256 ?state ?input] =>
    assert (precondition sha256 input repr)
  end.
  { simplify_spec sha256. cbn [reset_repr sha256_specification denote_type] in *.
    autorewrite with Nnat.
    logical_simplify; subst; try lia.

    destr (state =? 7); try lia.
    destr (state =? 6); try lia.
    destr (state =? 5); try lia.
    destr (state =? 4); try lia.
    destr (state =? 1); try lia.

    destr (state =? 3); logical_simplify; subst; try lia;
    [|destr (state =? 0); logical_simplify; subst; try lia;
    [|destr (state =? 2); logical_simplify; subst; try lia]].
    all:
      repeat (match goal with
                  | |- context [ ?X =? ?Y ] => destr ( X =? Y); try lia
                  | |- context [ ?X <=? ?Y ] => destr ( X <=? Y); try lia
                  | |- context [ ( ?X =? ?Y )%N ] => destr ( X =? Y)%N; try lia
                  | |- context [ ( ?X <=? ?Y )%N ] => destr ( X <=? Y)%N; try lia
                  end; try lia); boolsimpl.
    all: cbn [fst snd].
    all: try rewrite Tauto.if_same.
    all: rewrite ?List.app_nil_r.
    all: cbv [new_msg_bytes].
    all: try (destruct msg_complete); try (ssplit; lia).
    all: destruct sha_ready_circ.
    all: try (push_length; ssplit; lia).
    all: destruct fifo_valid.
    all: try (push_length; ssplit; lia).
    all: destruct fifo_final; try lia.
    all: try (push_length; ssplit; lia).
    all: destruct input_done; try lia.
  }

  ssplit.
  {
    cbn [fst snd] in *.
    match goal with
    | |- context [ @step ?i ?s ?o sha256 ?state ?input ] =>
        epose proof (@invariant_preserved_pf s i o sha256 ShaRepr _ _ sha256_correctness input state
        (msg, msg_complete, n, n0, n1, b) (l, b0, n2, n3, n4, b1) _ H0 H
        ) as HX
        ; remember (fst (@step i s o sha256 state input)) as step_sha
    end.

    cbn [denote_type absorb_any sha_block sha_digest sha_word fst snd] in *.
    destruct_products.
    repeat (inversion_prod; cbn [fst snd] in *).
    apply HX.
    Unshelve.
    cbn [update_repr sha256_specification].
    repeat (rewrite <- tup_if; cbn [fst snd]).
    repeat inversion_prod.
    subst.
    autorewrite with Nnat.
    destruct state.
    {
      repeat destr_nat_match.
      now cbn [fst snd].
    }
    destruct state.
    { repeat destr_nat_match.  }
    destruct state.
    {
      repeat destr_nat_match.
      repeat (rewrite <- tup_if; cbn [fst snd]).
      reflexivity.
    }
    destruct state.
    {
      replace (N.to_nat 4) with 4 by lia.
      replace (N.to_nat 5) with 5 by lia.
      replace (N.to_nat 6) with 6 by lia.
      repeat destr_nat_match.
      repeat destr_nat_match_hyp.
      subst.
      repeat (rewrite <- tup_if; cbn [fst snd]).
      destruct b.
      all: rewrite ?Tauto.if_same.
      { reflexivity. }
      { reflexivity. }
    }
    lia.
  }
  { repeat (destruct_one_match); lia. }
  { autorewrite with Nnat.
    destruct cmd_hmac_enable; try lia.
    { destruct state.
      { all: cbn; boolsimpl.
        now destruct cmd_hash_start.
      }
      lia.
    }

    destruct state; cbn [fst] in *.
    all: cbn; boolsimpl.
    { now destruct cmd_hash_start. }
    destruct state; cbn [fst] in *.
    { lia. }
    destruct state; [destruct b|]; cbn [fst] in *.
    all: cbn; boolsimpl.
    {
      destruct sha_ready_circ, fifo_valid; boolsimpl; cbn [fst]; try lia.
      all: destruct cmd_hash_process, fifo_final; boolsimpl; try lia.
    }
    {
      destruct fifo_final; logical_simplify; subst; try lia.
      all: repeat (destruct_one_match; try lia).
    }

    destruct state; cbn [fst] in *.
    all: cbn; boolsimpl.
    { destruct waiting_for_digest, sha_signaled_done;
      repeat destr_nat_match_hyp;
      subst; boolsimpl; try lia. }
    lia.
  }
  {
    destruct state.
    { destruct cmd_hash_start; destruct_one_match; cbn [fst snd]; congruence. }
    destruct state.
    { lia. }
    destruct state.
    {
      destr_nat_match.
      repeat destruct_one_inner_match; try lia.
    }
    destruct state; [|try lia].
    repeat destr_nat_match; repeat destruct_one_inner_match; try lia.
  }
  {
    destr (state =?0); try lia.
    {
      subst; cbn [fst snd].
      intros; logical_simplify; subst.
      trivial.
    }
    destr (state =?2).
    {
      destruct b0; [|trivial].
      logical_simplify; subst.
      repeat destr_nat_match_hyp; repeat destr_nat_match; repeat destruct_one_inner_match; try lia.
      all: destruct msg_complete; [lia|].
      all: repeat inversion_prod; revert H23; repeat (rewrite <- tup_if; cbn [fst snd]).
      all: destruct sha_ready_circ; try lia; boolsimpl.
      all: rewrite ?Tauto.if_same; now intros.
    }
    destr (state =? 3); try lia.
    subst state input_done.
    destruct b0; trivial.
  }

  {
    use_correctness' sha256.
    destruct state.
    {
      autorewrite with Nnat.
      repeat destr_nat_match.
      repeat destr_nat_match_hyp.
      now cbn.
    }

    destruct state.
    { destr_nat_match. }

    destruct state.
    {
      autorewrite with Nnat.
      repeat destr_nat_match.
      repeat destr_nat_match_hyp.
      cbn [fst snd] in *.

      subst; cbn [fst snd].
      cbv [andb].
      destruct sha_ready_circ, fifo_valid; boolsimpl; try reflexivity.
    }

    destruct state.
    {
      autorewrite with Nnat.
      replace (N.to_nat 4) with 4 by lia.
      replace (N.to_nat 5) with 5 by lia.
      repeat destr_nat_match.
      repeat destr_nat_match_hyp.
      cbn [fst snd] in *.
      subst.
      rewrite ?Tauto.if_same.
      reflexivity.
    }

    lia.
  }

  {
    use_correctness' sha256.
    destruct state.
    {
      replace ((if cmd_hash_start then 2 else 0) =? 3) with false
        by (destruct_one_match; destr_nat_match; lia).
      trivial.
    }

    destruct state.
    { destr_nat_match. }

    destruct state.
    {
      autorewrite with Nnat.
      repeat destr_nat_match.
      repeat destr_nat_match_hyp.
      cbn [fst snd] in *.
      boolsimpl.
      destruct sha_ready_circ, cmd_hash_process; boolsimpl; try reflexivity.
      destruct fifo_final; logical_simplify; subst; destr_nat_match; try lia.
      rewrite ?Tauto.if_same.
      destr_nat_match; boolsimpl.
      reflexivity.
    }

    destruct state.
    {
      autorewrite with Nnat.
      replace (N.to_nat 4) with 4 by lia.
      replace (N.to_nat 5) with 5 by lia.
      replace (N.to_nat 6) with 6 by lia.
      repeat destr_nat_match.
      repeat destr_nat_match_hyp.
      boolsimpl.
      cbn [fst snd] in *.
      boolsimpl.
      destruct cmd_hmac_enable; try lia.
      destruct sha_signaled_done, sha_ready_circ, cmd_hash_process;
        repeat (destr_nat_match; boolsimpl); try reflexivity.
      all: destruct b; boolsimpl; try reflexivity.
      all: rewrite ?Tauto.if_same.
      all: try reflexivity.

      all: destruct fifo_valid, waiting_for_digest; boolsimpl; repeat destr_nat_match; try reflexivity.
      all: subst; try lia.
    }

    lia.
  }

  {
    assert (forall {A} (ls: list A), length ls > 0 -> ls <> []) as Hx.
    { clear; intros; now destruct ls. }

    destruct state.
    { repeat destr_nat_match.
      destruct cmd_hash_start; destr_nat_match; reflexivity.
    }
    destruct state.
    { repeat destr_nat_match. }
    destruct state.
    {
      repeat destr_nat_match.
      repeat destr_nat_match_hyp.

      destruct sha_ready_circ; repeat destr_nat_match.
      {
        assert ((if cmd_hash_process then if fifo_final then 3 else 2 else 2) =? 0 = false).
        { repeat destruct_one_inner_match; destr_nat_match. }
        rewrite H11.
        destruct new_has_content.
        {
          repeat inversion_prod.
          logical_simplify; subst.
          autorewrite with tuple_if.
          cbn [fst snd].
          split.
          { now rewrite ?Tauto.if_same. }
          { repeat destruct_one_inner_match; cbn [new_msg_bytes]; try trivial.
            all: apply Hx; push_length.
            all: destruct msg; try congruence.
            all: cbn [length]; lia.
          }
        }
        destruct fifo_valid; try trivial.
        repeat inversion_prod.
        subst.
        autorewrite with tuple_if.
        cbn [fst snd].
        split.
        { rewrite ?Tauto.if_same. now destruct b. }
        { apply Hx; destruct b; cbn [new_msg_bytes].
          { destruct fifo_final; length_hammer. }
          repeat destruct_one_inner_match.
          all: try length_hammer.
          all: simplify_invariant sha256; logical_simplify; subst.
          all: try congruence.
          all: try (destruct msg_complete; logical_simplify; subst; try lia).
        }
      }
      repeat inversion_prod.
      subst.
      autorewrite with tuple_if.
      cbn [fst snd].
      destruct new_has_content; try lia.
      logical_simplify; subst.
      split.
      { now rewrite ?Tauto.if_same. }
      repeat destruct_one_inner_match; trivial.
    }
    destruct state; try lia.
    destruct sha_signaled_done; destr_nat_match.
    destruct new_has_content; [|destruct sha_ready_circ, fifo_valid]; try trivial.
    all: repeat inversion_prod; subst; autorewrite with tuple_if; cbn [fst snd];
          logical_simplify; subst; split;

      [ rewrite ?Tauto.if_same |
      repeat destruct_one_inner_match; trivial].
    { reflexivity. }
    all: destr_nat_match_hyp; logical_simplify; subst.
    all: congruence.
  }

  {
    destruct state.
    { destruct_one_inner_match; destr_nat_match; trivial. }
    destruct state; try lia.
    destruct state.
    { repeat destruct_one_inner_match; repeat destr_nat_match; try lia.
      trivial.
    }
    destruct state; try lia.
    { repeat destruct_one_inner_match; repeat destr_nat_match; try lia.
    }
  }

  {
    assert (forall {A} (ls: list A), length ls > 0 -> ls <> []) as Hx.
    { clear; intros; now destruct ls. }
    destruct state.
    { destruct_one_inner_match; destr_nat_match; trivial. }

    destruct state; try lia.
    destruct state.
    { repeat destruct_one_inner_match; repeat destr_nat_match;
        repeat destr_nat_match_hyp; logical_simplify; subst; try trivial.
      destruct msg_complete; logical_simplify; subst; try lia.
      destruct input_done; logical_simplify; subst; try lia.

      repeat inversion_prod.
      destruct new_has_content.
      all: subst; autorewrite with tuple_if; cbn [fst snd].
      all: logical_simplify; subst.
      all: simplify_invariant sha256.
      all: repeat destruct_one_inner_match; try trivial.
      all: apply Hx; cbn [new_msg_bytes]; push_length; try lia.

    }

    destruct state; try destruct_one_inner_match; repeat destr_nat_match; try lia.
    {
      repeat inversion_prod.
      subst; autorewrite with tuple_if; cbn [fst snd].
      simplify_invariant sha256.
      repeat destruct_one_inner_match; try trivial.
      repeat destr_nat_match_hyp; logical_simplify; subst.
    }
  }

  { destruct state.
    { repeat destr_nat_match.
      destruct cmd_hash_start; destr_nat_match; reflexivity.
    }
    destruct state.
    { repeat destr_nat_match. }
    destruct state.


    { repeat destr_nat_match.
      destruct sha_ready_circ, cmd_hash_process, fifo_final; destr_nat_match.
      all: try reflexivity.
      autorewrite with Nnat.
      repeat destr_nat_match.
      boolsimpl.
      destruct cmd_hmac_enable; try lia.
      use_correctness' sha256.
      cbn [fst snd negb].
      simplify_invariant sha256.
      destr_nat_match.
      destruct b; now boolsimpl.
    }
    destruct state.
    {
      use_correctness' sha256.
      repeat destr_nat_match.
      destruct sha_signaled_done.
      { now repeat destr_nat_match. }
      repeat destr_nat_match.
      cbn [fst snd].
      simplify_invariant sha256.
      destruct b; boolsimpl.
      { logical_simplify; subst.
        split; [reflexivity|].
        destruct cmd_hmac_enable; try lia.
      }
      logical_simplify; subst.
      repeat inversion_prod.
      autorewrite with tuple_if in H6.
      cbn [fst snd] in *.
      rewrite ?Tauto.if_same in H6.
      subst.
      rewrite ?Tauto.if_same.
      match goal with
      | |- match (if ?X then _ else _) with _ => _ end => destr X
      end.
      {
        split; try reflexivity. subst.
        rewrite ?Tauto.if_same.
        split; try reflexivity.

        autorewrite with Nnat in *.
        replace (N.to_nat 4) with 4 in * by lia.
        replace (N.to_nat 5) with 5 in * by lia.
        repeat destr_nat_match_hyp.
        cbn [fst] in *.
        destruct sha_ready_circ; try trivial.
      }
      rewrite ?Tauto.if_same.

      destruct cmd_hmac_enable;try lia.
      autorewrite with Nnat.
      replace (N.to_nat 4) with 4 by lia.
      replace (N.to_nat 5) with 5 by lia.
      replace (N.to_nat 6) with 6 by lia.
      repeat destr_nat_match.
      destruct waiting_for_digest; try lia.
      now boolsimpl.
    }
    lia.
  }

Qed.

Lemma hmac_inner_output_correct :
  output_correct hmac_inner.
Proof.
  simplify_invariant hmac_inner. cbn [absorb_any].
  simplify_spec hmac_inner.

  intros input state repr new_repr.
  pose (input_:=input). pose (state_:=state). pose (repr_:=repr). pose (new_repr_:=new_repr).
  revert dependent repr. revert dependent state. revert dependent input.

  intros (fifo_valid, (fifo_data, (fifo_length, (fifo_final,
         (cmd_hash_start, (cmd_hash_process, (cmd_hmac_enable, (hmac_key_vec, [])))))))).
  intro.
  intros
      ( (finishing, (waiting_for_digest, (accept_fifo, (ptr, (inner_state, (digest_circ, sha_ready_circ))))))
      , sha_state_circ).
  intro.
  intros (((((((state, input_done), raised_process), sha_signaled_done), sha_ready), digest), has_content), sha_repr).
  intro.
  destruct sha_repr as (((((msg,msg_complete),?),?),?),?).
  destruct sha_state_circ as ((ready, (?, (?, (?, ?)))), (padder, inner)).
  destruct padder as (?, (?, (?, (?, (?, ?))))).
  destruct inner as (?, (?, (?, ?))).
  intros.

  (* for some reason the modulo expands into ugly match statement wihtout this *)
  remember (n mod 64) as n_mod_64.
  logical_simplify. subst.

  cbv [hmac_inner K]. cbn [negb]. stepsimpl.
  repeat (destruct_inner_pair_let; cbn [fst snd]).

  lazymatch goal with
  | H : sha256_invariant ?state ?repr
    |- context [step sha256 ?state ?input] =>
    assert (precondition sha256 input repr)
  end.
  { simplify_spec sha256. cbn [reset_repr sha256_specification denote_type] in *.
    autorewrite with Nnat.
    logical_simplify; subst; try lia.

    destr (state =? 7); try lia.
    destr (state =? 6); try lia.
    destr (state =? 5); try lia.
    destr (state =? 4); try lia.
    destr (state =? 1); try lia.

    destr (state =? 3); logical_simplify; subst; try lia;
    [|destr (state =? 0); logical_simplify; subst; try lia;
    [|destr (state =? 2); logical_simplify; subst; try lia]].
    all:
      repeat (match goal with
                  | |- context [ ?X =? ?Y ] => destr ( X =? Y); try lia
                  | |- context [ ?X <=? ?Y ] => destr ( X <=? Y); try lia
                  | |- context [ ( ?X =? ?Y )%N ] => destr ( X =? Y)%N; try lia
                  | |- context [ ( ?X <=? ?Y )%N ] => destr ( X <=? Y)%N; try lia
                  end; try lia); boolsimpl.
    all: cbn [fst snd].
    all: try rewrite Tauto.if_same.
    all: rewrite ?List.app_nil_r.
    all: cbv [new_msg_bytes].
    all: try (destruct msg_complete); try (ssplit; lia).
    all: destruct sha_ready_circ.
    all: try (push_length; ssplit; lia).
    all: destruct fifo_valid.
    all: try (push_length; ssplit; lia).
    all: destruct fifo_final; try lia.
    all: try (push_length; ssplit; lia).
    all: destruct input_done; try lia.
  }

  Ltac use_correctness' c :=
    lazymatch goal with
    | |- context [ @snd ?A ?B (@step ?i ?s ?o c ?state ?input) ] =>
      find_correctness c;
      pose proof (@output_correct_pf
                    s i o c _ _ _ _
                    input state _ ltac:(eassumption) ltac:(eassumption));
      generalize dependent (@snd A B (@step i s o c state input)); intros;
      try simplify_postcondition c
      (* ; logical_simplify *)
      (* ; subst *)
    end.
  use_correctness' sha256.

  destruct H24 as [sha_done].
  destruct H24 as [sha_digest].
  destruct H24 as [sha_ready].
  logical_simplify.

  eexists (match digest with Some _ => true | _ => false end).
  eexists (match digest with Some x => x | _ =>
      match state with
      | 0 => _
      | 2 => _
      | 3 => _
      | _ => SHA256.H0
      end
     end).

  ssplit.
  {
    autorewrite with Nnat in *.
    destruct state; cbn [fst snd].
    { logical_simplify; subst; repeat destr_nat_match; boolsimpl.
      cbn [fst snd].
      subst.
      reflexivity.
    }
    destruct state; [lia|].
    destruct state; cbn [fst snd].
    { logical_simplify; subst; repeat destr_nat_match; boolsimpl.
      cbn [fst snd].
      subst.
      apply f_equal.
      destruct cmd_hmac_enable; try lia.
      assert ((if (sha_ready_circ && cmd_hash_process && fifo_final)%bool then 3 else 2) =? 0 = false)
       by (destruct sha_ready_circ, cmd_hash_process, fifo_final; cbn [andb]; destr_nat_match).
      rewrite H4.
      apply f_equal.

      reflexivity.
    }

    destruct state; cbn [fst snd].
    {
      simplify_invariant sha256.
      repeat destr_nat_match.
      boolsimpl.
      destruct cmd_hmac_enable; try lia.
      apply f_equal.
      destruct digest, waiting_for_digest; logical_simplify; try lia.
      2:{ logical_simplify; subst; boolsimpl; reflexivity. }
      logical_simplify; subst; boolsimpl.

      repeat destr_nat_match.
      autorewrite with Nnat.
      replace (N.to_nat 4) with 4 in * by lia.
      replace (N.to_nat 5) with 5 in * by lia.
      replace (N.to_nat 6) with 6 in * by lia.
      repeat destr_nat_match.
      cbn [fst snd].

      apply f_equal.
      destruct b; try lia.
      rewrite Tauto.if_same.
      simplify_invariant sha256.
      repeat destruct_one_inner_match; try reflexivity.
      all: try lia.
      all: cbn [fst] in *.
      all: rewrite Tauto.if_same in H32.
      all: trivial.
    }
    lia.
  }

  destruct digest; split; reflexivity.
Qed.


Existing Instances hmac_inner_invariant_preserved hmac_inner_output_correct hmac_inner_invariant_at_reset.

Global Instance hmac_inner_correctness : correctness_for hmac_inner.
Proof. constructor; try typeclasses eauto. Defined.
