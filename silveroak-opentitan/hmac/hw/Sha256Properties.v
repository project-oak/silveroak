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
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.Byte.
Require Import Cava.Util.If.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.
Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Invariant.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import HmacSpec.SHA256Properties.
Require Import HmacHardware.Sha256.
Require Import HmacHardware.Sha256InnerProperties.
Require Import HmacHardware.Sha256PadderProperties.
Require HmacSpec.SHA256.
Import ListNotations.

Require Import coqutil.Tactics.autoforward.
Ltac autoforward_in db H ::=
  let tmp := fresh H in
  rename H into tmp;
  let A := type of tmp in
  pose proof ((ltac:(typeclasses eauto with db) : autoforward A _) tmp) as H;
  (* Recently, this `move` was added in coqutil, which breaks this proof script,
     because through destruct_one_match_hyp, it depends on the hypotheses order,
     and the most straightforward way to fix the broken proofs requires too
     much memory to work on CI *)
  (* move H after tmp; *)
  clear tmp.

(* Higher-level representation for sha256:
   msg : message so far
   msg_complete : whether the message is complete
   byte_index : index indicating the last byte the padder has gotten to
   t : compression round index
   cleared : whether the circuit is cleared
 *)
Instance sha256_invariant
  : invariant_for sha256 (list byte * bool * nat * nat * nat * bool) :=
  fun (state : denote_type ((Bit ** sha_block ** sha_digest ** BitVec 6 ** Bit)
                            ** state_of sha256_padder
                            ** state_of sha256_inner))
    repr =>
    let '((ready, (block, (digest, (count, done)))),
          (sha256_padder_state, sha256_inner_state)) := state in
    let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := repr in
    (* block index is byte_index / 64 (64 bytes per block) *)
    let padder_block_index := padder_byte_index / 64 in
    let inner_block_index := inner_byte_index / 64 - 1 in
    (* compute representation for padder state *)
    let padder_repr :=
        if cleared
        then (reset_repr (c:=sha256_padder))
        else (msg, msg_complete,
              padder_byte_index =? padded_message_size msg, padder_byte_index) in
    (* compute representation for inner *)
    let inner_repr :=
        if cleared
        then (reset_repr (c:=sha256_inner))
        else
          (firstn (inner_byte_index / 64 * 16) (SHA256.padded_msg msg)
           , inner_block_index
           , t
           , if t =? 64 then true else inner_byte_index =? 0
           , inner_byte_index =? 0) in
    (* index of the block that's currently in progress (i.e. next block whose
       digest will be produced) *)
    let completed_block_index :=
        if (count <=? 15)%N
        then
          (* padder is running; same block index the padder is on *)
          padder_block_index
        else if (count =? 16)%N
             then
               (* padder is done, so padder_block_index has just moved to the
                  next block; subtract 1 to get the current index *)
               padder_block_index - 1
             else
               if t =? 64
               then
                 (* inner circuit is done; next block to be produced will be
                    whatever block index the padder is on *)
                 padder_block_index
               else
                 (* inner circuit is in progress; next block to be produced will
                    be whatever block index the inner circuit is on *)
                 inner_block_index in
    (* the invariant for sha256_padder is satisfied *)
    sha256_padder_invariant sha256_padder_state padder_repr
    (* ...and the invariant for sha256_inner is satisfied *)
    /\ sha256_inner_invariant sha256_inner_state inner_repr
    (* ...and the length of [block] is always 16 *)
    /\ length block = 16
    (* ...and count is always in the range [0,17] *)
    /\ (count <= 17)%N
    (* ...and byte indices are always at a word boundary *)
    /\ padder_byte_index mod 4 = 0
    /\ (if cleared
       then
         (* if the circuit is cleared, it must be in the reset state
            (including subcircuits) *)
         padder_byte_index = 0
         /\ inner_byte_index = 0
         /\ t = 0
         /\ msg = []
         /\ msg_complete = false
         /\ count = 0%N
         /\ done = true
         /\ digest = SHA256.H0
       else
         (* the byte index (padder counter) is within the range
            [4,padded_message_size msg] *)
         4 <= padder_byte_index <= padded_message_size msg
         (* ...and t (inner loop counter) is in the range [0,64] *)
         /\ t <= 64
         (* ...and ready is true iff count < 16 *)
         /\ ready = (count <? 16)%N
         (* ...and the digest must be the expected digest (digest is only
            stored at the end of each inner loop) *)
         /\ digest = fold_left (SHA256.sha256_step msg)
                              (seq 0 completed_block_index) SHA256.H0
         (* ...and the index is past the end of the message iff the message is
            complete *)
         /\ (if msg_complete then length msg <= padder_byte_index else padder_byte_index = length msg)
         (* ...and if [done] is true, we must be at the end of the message *)
         /\ (if done
            then padder_byte_index = inner_byte_index
                 /\ padder_byte_index = padded_message_size msg
                 /\ count = 0%N
                 /\ t = 64
            else True)
         (* ...and the state variables agree with [count] *)
         /\ (if (count <=? 15)%N
            then
              (* padder is running *)
              skipn (16 - N.to_nat count) block
              = List.slice 0%N (SHA256.padded_msg msg) (padder_block_index * 16) (N.to_nat count)
              /\ padder_byte_index mod 64 = N.to_nat count * 4 (* byte_index is on the [count]th word *)
              /\ (if (padder_byte_index <? 64) then t = 0 else t = 64) (* inner is between blocks *)
              /\ inner_byte_index = padder_block_index * 64
            else
              (* inner loop is running or about to run *)
              padder_byte_index mod 64 = 0 (* byte index is at the end of a block *)
              /\ (if (count =? 16)%N
                 then
                   (* padder has just finished a block; send the completed
                        block to start inner loop *)
                   block = List.slice 0%N (SHA256.padded_msg msg)
                                      (inner_byte_index / 64 * 16) 16
                   /\ (if (padder_byte_index =? 64) then t = 0 else t = 64)
                   /\ padder_byte_index = inner_byte_index + 64
                 else
                   (* inner loop is in progress *)
                   0 <= t < 64
                   /\ inner_byte_index = padder_byte_index))
      ).

Instance sha256_specification
  : specification_for sha256 (list byte * bool * nat * nat * nat * bool) :=
  {| reset_repr := ([], false, 0, 0, 0, true);
     update_repr :=
       fun (input : denote_type [Bit; sha_word; Bit; BitVec 4; Bit])
         repr =>
         let '(fifo_data_valid,
               (fifo_data, (is_final, (final_length, (clear, _))))) := input in
         let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := repr in
         let new_bytes :=
             new_msg_bytes fifo_data_valid fifo_data is_final final_length in
         if clear
         then ([], false, 0, 0, 0, true)
         else if cleared
              then if fifo_data_valid
                   then (new_bytes, is_final, 4, 0, 0, false)
                   else ([], false, 0, 0, 0, true) (* stay in cleared state *)
              else if (padder_byte_index =? inner_byte_index)
                   then if t =? 64
                        then
                          (* sha256_inner has finished; start the padder on the
                             next block if we can *)
                          if (padder_byte_index =? padded_message_size msg)
                          then
                            (* padder is at the end of the message and
                               processing is completely done; hold state
                               constant *)
                            repr
                          else
                            if msg_complete
                            then
                              (* step padder *)
                              (msg, msg_complete, padder_byte_index + 4, inner_byte_index, t, cleared)
                            else if fifo_data_valid
                                 then
                                   (* step padder *)
                                   (msg ++ new_bytes, is_final, padder_byte_index + 4, inner_byte_index, t, cleared)
                                 else
                                   (* message is incomplete and next word isn't
                                      available; wait *)
                                   repr
                        else
                          (* sha256_inner is already in progress; increment t *)
                          (msg, msg_complete, padder_byte_index, inner_byte_index, S t, cleared)
                   else
                     if (padder_byte_index =? inner_byte_index + 64)
                     then
                       (* padder just finished a block; start sha256_inner by
                          passing in the new block and reset t to 0 *)
                       (msg, msg_complete, padder_byte_index, padder_byte_index, 0, cleared)
                     else
                       (* padder is midway through a block; take another step if possible *)
                       if msg_complete
                       then
                         (* step padder *)
                         (msg, msg_complete, padder_byte_index + 4, inner_byte_index, t, cleared)
                       else if fifo_data_valid
                            then
                              (* step padder *)
                              (msg ++ new_bytes, is_final, padder_byte_index + 4, inner_byte_index, t, cleared)
                            else
                              (* message is incomplete and next word isn't
                                 available; wait *)
                              (msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared);
     precondition :=
       fun (input : denote_type [Bit; sha_word; Bit; BitVec 4; Bit])
         repr =>
         let '(fifo_data_valid,
               (fifo_data, (is_final, (final_length, (clear, _))))) := input in
         let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := repr in
         let new_bytes :=
             new_msg_bytes fifo_data_valid fifo_data is_final final_length in
         (* the total message length (including any new data) cannot exceed 2 ^
            64 bits (2^61 bytes) -- using N so Coq doesn't try to compute 2 ^ 61
            in nat *)
         (N.of_nat (length (msg ++ new_bytes)) < 2 ^ 61)%N
         (* ...and if data is valid, it must be in expected range *)
         /\ (if fifo_data_valid
            then if is_final
                 then (fifo_data < 2 ^ (8 * final_length))%N
                      /\ (1 <= final_length <= 4)%N
                 else (fifo_data < 2 ^ 32)%N
            else True)
         (* ...and if msg_complete is true, then new valid data cannot be passed
            (must clear first) *)
         /\ (if msg_complete then fifo_data_valid = false else True);
     postcondition :=
       fun (input : denote_type [Bit; sha_word; Bit; BitVec 4; Bit])
         repr (output : denote_type (Bit ** sha_digest ** Bit)) =>
         let '(fifo_data_valid,
               (fifo_data, (is_final, (final_length, (clear, _))))) := input in
         let '(msg, msg_complete, padder_byte_index, inner_byte_index, t, cleared) := repr in
         (* new value of [cleared] *)
         let is_cleared := if clear
                           then true
                           else if cleared
                                then negb (fifo_data_valid)
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

         exists done digest ready,
           output = (done, (digest, ready))
           /\ done = is_cleared_or_done
           /\ ready = is_ready
           /\ if is_cleared
             then digest = SHA256.H0
             else if is_cleared_or_done
                  then digest = BigEndianBytes.bytes_to_Ns
                                  4 (SHA256.sha256 msg)
                  else True (* no guarantees about intermediate output *)
  |}.

Lemma sha256_invariant_at_reset : invariant_at_reset sha256.
Proof.
  simplify_invariant sha256.
  cbn [reset_repr reset_state sha256 sha256_specification
                  sha256_padder_specification
                  sha256_inner_specification].
  stepsimpl. cbn [Nat.eqb]. compute_expr (0 mod 64).
  ssplit;
    lazymatch goal with
    | |- sha256_padder_invariant _ _ => apply sha256_padder_invariant_at_reset
    | |- sha256_inner_invariant _ _ => apply sha256_inner_invariant_at_reset
    | _ => reflexivity || lia
    end.
Qed.

Lemma test_nth_byte_of_x x i :
  (x < 2 ^ 32)%N ->
  N.testbit
  (Byte.to_N
     (nth (N.to_nat (i / 8))
        [N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 3) * 8));
        N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 2) * 8));
        N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 1) * 8));
        N_to_byte (N.shiftr x (N.of_nat (4 - 1 - 0) * 8))] "000"%byte))
  (i mod 8) = N.testbit x i.
Proof.
  intros.
  remember (N.to_nat (i/8)) as m.
  destr (m <? 4).
  {
  repeat (destruct m as [|m]; try prove_by_zify);
    cbn [List.app nth Nat.mul Nat.add];
    rewrite N2Byte.id;
    replace 256%N with (2^8)%N by now cbn.
  { assert(i < 8)%N by prove_by_zify.
    rewrite N.mod_small with (b:=8%N) by lia.
    testbit_crush.
  }
  { assert(i - 8 < 8)%N by prove_by_zify.
    replace (i mod 8)%N with ((i - 8) mod 8)%N by prove_by_zify.
    rewrite N.mod_small with (b:=8%N) by lia.
    cbn [Nat.sub].
    testbit_crush.
    now replace ((i - 8 + N.of_nat 1 * 8))%N with i by prove_by_zify.
  }
  { assert(i - 16 < 8)%N by prove_by_zify.
    replace (i mod 8)%N with ((i - 16) mod 8)%N by prove_by_zify.
    rewrite N.mod_small with (b:=8%N) by lia.
    cbn [Nat.sub].
    testbit_crush.
    now replace ((i - 16 + N.of_nat 2 * 8))%N with i by prove_by_zify.
  }
  { assert(i - 24 < 8)%N by prove_by_zify.
    replace (i mod 8)%N with ((i - 24) mod 8)%N by prove_by_zify.
    rewrite N.mod_small with (b:=8%N) by lia.
    cbn [Nat.sub].
    testbit_crush.
    now replace ((i - 24 + N.of_nat 3 * 8))%N with i by prove_by_zify.
  }
  }
  assert (32 <= i)%N by prove_by_zify.
  rewrite nth_overflow by now push_length.
  destr (x=?0)%N;subst;push_Ntestbit;[reflexivity|].
  apply N.log2_lt_pow2 in H.
  { rewrite N.bits_above_log2; lia. }
  lia.
Qed.

Lemma concat_digest_to_N_id xs:
  Forall (fun x => x < 2 ^ 32)%N xs ->
  length xs = 8 ->
  BigEndianBytes.bytes_to_Ns 4 (SHA256.concat_digest xs) = xs.
Proof.
  intros.
  cbv [SHA256.concat_digest SHA256.w].
  cbv [seq SHA256.w].
  replace (N.to_nat 32 / 8) with 4 by prove_by_zify.

  repeat (destruct xs as [ | ?x xs];[now cbn in *| cbn in H0;
    let h := fresh in pose proof (Forall_inv H) as h;
    cbn beta in h;
    let h' := fresh in
    pose proof (Forall_inv_tail H) as h';
    clear H; rename h' into H;
    try lia]).
  clear H.
  destruct xs;[|cbn in H0; lia].

  apply nth_ext with (d:=0%N) (d':=0%N).
  { now cbn. }
  intros.
  cbv [SHA256.concat_digest].
  rewrite nth_bytes_to_Ns; cycle 1.
  { now cbn.  }
  { lia. }

  revert H.
  rewrite flat_map_concat_map.
  cbv [seq].
  cbn [List.map seq nth Nat.mul Nat.add concat List.app].
  cbv [BigEndianBytes.N_to_bytes seq BigEndianBytes.bytes_to_Ns ].
  push_length; intros.
  cbv [List.map].
  repeat (destruct n; [
    cbn [List.app nth Nat.mul Nat.add];
    apply N.bits_inj; intro i;
    rewrite concat_bytes_spec;
    apply test_nth_byte_of_x; trivial
  |]).
  exfalso; prove_by_zify.
Qed.

Require Import Coq.derive.Derive.

(* simplifies the sha256 circuit so we don't have to wait for the slow
   simplifications in every proof *)
Derive step_sha256_simplified
       SuchThat
       (forall ready block digest count done sha256_padder_state sha256_inner_state
          fifo_data_valid fifo_data is_final final_length clear,
           let state := ((ready, (block, (digest, (count, done)))),
                         (sha256_padder_state, sha256_inner_state)) in
           let input := (fifo_data_valid,
                         (fifo_data, (is_final, (final_length, (clear, tt))))) in
           step sha256 state input =
           step_sha256_simplified ready block digest count done sha256_padder_state sha256_inner_state
                                  fifo_data_valid fifo_data is_final final_length clear)
       As step_sha256_simplified_eq.
Proof.
  cbv [sha256]; intros; stepsimpl.
  repeat (destruct_inner_pair_let; cbn [fst snd]).
  rewrite <-!tup_if. cbn [fst snd].
  subst step_sha256_simplified. instantiate_app_by_reflexivity.
Qed.

Lemma sha256_invariant_preserved : invariant_preserved sha256.
Proof.
  simplify_invariant sha256. cbn [absorb_any].
  simplify_spec sha256.
  (* The following gymnastics results in input_, state_, and repr_ being posed
     as let-hypotheses, which makes proof debugging easier because one can look
     at them and see what case the proof is dealing with *)
  intros input state repr.
  pose (input_:=input). pose (state_:=state). pose (repr_:=repr).
  revert dependent repr. revert dependent state. revert dependent input.
  intros (fifo_data_valid,
          (fifo_data, (is_final, (final_length, (clear, []))))).
  intro.
  intros ((ready, (block, (digest, (count, done)))),
          (sha256_padder_state, sha256_inner_state)).
  intro.
  intros (((((msg, msg_complete), padder_byte_index), inner_byte_index), t), cleared).
  intros; logical_simplify; subst.

  rewrite step_sha256_simplified_eq. cbv [step_sha256_simplified]. cbn [fst snd].
  rewrite <-!tup_if. cbn [fst snd].

  (* A whole bunch of assertions about the properties of padded_message_size
     related to all 3 possible next messages *)
  pose proof padded_message_size_mono
       msg (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_bytes_longer_than_input msg.
  pose proof padded_message_bytes_longer_than_input
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_bytes_longer_than_input
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof min_padded_message_size msg.
  pose proof min_padded_message_size
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof min_padded_message_size
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_size_modulo msg.
  pose proof padded_message_size_modulo
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_size_modulo
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).

  (* prove that padder precondition is satisfied *)
  lazymatch goal with
  | H : sha256_padder_invariant ?state ?repr
    |- context [step sha256_padder ?state ?input] =>
    assert (precondition sha256_padder input repr)
  end.
  { simplify_spec sha256_padder. cbn [reset_repr sha256_padder_specification].
    destr cleared; logical_simplify; subst;
      [ destr fifo_data_valid; destr is_final; logical_simplify; subst;
        ssplit; solve [auto] | ].
    ssplit; [ assumption | ].
    destr fifo_data_valid; logical_simplify; subst; [ | tauto ].
    destr is_final; logical_simplify; subst; split; try tauto.
    { destruct msg_complete; try lia. }
    { destruct msg_complete; try lia. }
  }

  use_correctness' sha256_padder.
  cbn [reset_repr sha256_padder_specification] in *.

  (* prove that inner precondition is satisfied *)
  lazymatch goal with
  | H : sha256_inner_invariant ?state ?repr
    |- context [step sha256_inner ?state ?input] =>
    assert (precondition sha256_inner input repr)
  end.
  { simplify_spec sha256_inner. cbn [reset_repr sha256_inner_specification].
    destr cleared; logical_simplify; subst;
      [ destr fifo_data_valid; destr is_final; logical_simplify; subst;
        ssplit; solve [auto] | ].
    rewrite fold_left_sha256_step_alt_firstn.
    all:destr (t =? 64); logical_simplify; subst; try lia.
    all:destr (count <=? 15)%N; logical_simplify; subst.
    all:destr (count =? 16)%N; logical_simplify; subst; try lia.
    all:repeat (destruct_one_match; logical_simplify; subst; try lia).
    all:repeat lazymatch goal with
               | H : (Nat.eqb ?x ?y) = false |- _ => apply Nat.eqb_neq in H
               end.
    all:try (destr (padder_byte_index <? 64); logical_simplify; subst; [ | lia ]).
    all:rewrite ?Nat.div_mul, ?Nat.div_small in * by lia.
    all:try reflexivity.
    all:try discriminate.
    all:natsimpl.
    all:repeat lazymatch goal with
               | |- context [(?x + ?y) / ?y] => replace ((x + y) / y) with (x / y + 1) by prove_by_zify
               | |- context [S (?x - 1)] => replace (S (x - 1)) with x by prove_by_zify
               end.
    all:natsimpl.
    all:try (destr (inner_byte_index + 64 =? 64); logical_simplify; subst; lia).
    all:lazymatch goal with
        | |- _ /\ _ /\ _ => ssplit; [ reflexivity | | length_hammer ]
        | _ => idtac
        end.
    all:rewrite ?firstn_slice_app by (push_length; prove_by_zify).
    all:lazymatch goal with
        | |- fold_left _ _ _ = fold_left _ _ _ =>
          eapply fold_left_ext_In; intros *;
            rewrite in_seq; intros;
              rewrite !sha256_step_alt_firstn by lia;
              try reflexivity
        end. }

  use_correctness' sha256_inner.
  cbn [reset_repr sha256_inner_specification] in *.

  ssplit.
  { (* prove that padder invariant is preserved *)
    eapply invariant_preserved_pf; [ | eassumption .. ].
    (* prove that padder state rep is updated correctly *)
    cbn [reset_repr update_repr sha256_padder_specification] in *.
    destr clear; [ destruct cleared; reflexivity | ].
    destr cleared; logical_simplify; subst.
    { (* cleared=true *)
      destr fifo_data_valid; logical_simplify; subst;
        [ | destruct_one_match; reflexivity ].
      repeat (destruct_one_match; try lia); try reflexivity; [ ].
      lazymatch goal with
      | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
      end.
      reflexivity. }
    { (* cleared=false *)
      destr fifo_data_valid; logical_simplify; subst;
      cbn [Nat.eqb].
      { (* data_valid=true *)
        rewrite ?Tauto.if_same.
        destr (length msg =? padded_message_size msg); [ lia | ].
        destr (count <=? 15)%N; logical_simplify; subst;
          [ destr (count =? 0)%N; logical_simplify; subst
          | destr (count =? 16)%N; logical_simplify; subst ].
        all:try lia.
        all:cbn [N.eqb Pos.eqb Nat.eqb] in *.
        all:repeat destruct_one_match; try lia.
        all:repeat lazymatch goal with
                   | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                   end.
        all:try reflexivity.
        all:try prove_by_zify.
        { destruct msg_complete; try lia. }
        { destruct msg_complete; try lia. }
        { destruct_one_match_hyp; logical_simplify; subst; try lia.
          repeat (destruct_one_match_hyp; logical_simplify; subst; try lia).
        }

      }
      { (* data_valid = false *)
        destr msg_complete; logical_simplify; subst;
        rewrite ?Tauto.if_same; [ | repeat destruct_one_match; reflexivity ].
        assert (padder_byte_index mod 64 = 0 ->
                padder_byte_index + 4 <> padded_message_size msg) by prove_by_zify.
        repeat (destruct_one_match; try lia); logical_simplify; subst.
        all:rewrite ?Nat.eqb_refl; try reflexivity.
        all:repeat lazymatch goal with
                   | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                   end.
        all:destr (count =? 16)%N; subst; try lia.
        all:try (exfalso; prove_by_zify).
        all:destr (padder_byte_index <? 64); lia. } } }

  Optimize Proof.
  { (* prove that inner invariant is preserved *)
    eapply invariant_preserved_pf; [ | eassumption .. ].
    (* prove that inner state rep is updated correctly *)
    cbn [reset_repr update_repr sha256_inner_specification].
    destr clear; [ destr cleared; reflexivity | ].
    destr cleared; logical_simplify; subst;
      [ cbn [N.leb N.compare] in *; logical_simplify; subst;
        destr fifo_data_valid; logical_simplify; subst; reflexivity | ].

    destr (padder_byte_index =? padded_message_size msg); logical_simplify; subst.
    { (* padder has reached end of message *)
      (* only one possible case for data_valid and msg_complete;
         data_valid=false and msg_complete=true *)
      abstract(
      destr fifo_data_valid; destr msg_complete;
        logical_simplify; subst; try lia; [ ];
      destr (count <=? 15)%N; logical_simplify; subst;
      rewrite ?Tauto.if_same in *; cbn [fst snd] in *;
      boolsimpl;
      repeat (first [ destruct_one_match | destruct_one_match_hyp];
                  logical_simplify; subst; try lia; try reflexivity);
      try (exfalso; prove_by_zify);
      repeat lazymatch goal with
                 | H : (Nat.eqb ?x ?y) = true |- _ => apply Nat.eqb_eq in H; subst; try lia
                 | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                 | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                 end;
      try reflexivity;
      rewrite firstn_slice_app by (push_length; prove_by_zify);
      (* structure already matches; use prove_by_zify for nat arguments *)
      repeat (f_equal; lazymatch goal with
                           | |- @eq nat _ _ => prove_by_zify
                           | _ => idtac
                         end)).
    }
    { (* padder is not yet at end of message *)
      rewrite Tauto.if_same.

      destr (padder_byte_index =? inner_byte_index); logical_simplify; subst.
      { (* inner is running or just finished running *)
        all: repeat
            (repeat lazymatch goal with
                     | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                     | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                      end;
             try reflexivity;
             (destruct_one_match_hyp; logical_simplify; subst; try lia)).
        all: now rewrite firstn_padded_msg_truncate by prove_by_zify.
      }

      { (* padder is running or just finished running *)
        destr (padder_byte_index =? inner_byte_index + 64); logical_simplify; subst.
        { (* padder just finished running (count=16) *)
          destr (count <=? 15)%N; logical_simplify; subst;
            [ exfalso; prove_by_zify | ].
          destr (count =? 16)%N; [ | exfalso; prove_by_zify ].

          all: repeat
              (repeat lazymatch goal with
                       | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                       | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                        end;
               try reflexivity;
               (destruct_one_match_hyp; logical_simplify; subst; try lia)).

          all:repeat destruct_one_match; logical_simplify; subst; try lia.
          all:rewrite ?firstn_slice_app by (push_length; prove_by_zify).
          all:rewrite ?Nat.eqb_refl in *; try discriminate.
          all:repeat (f_equal; lazymatch goal with
                               | |- @eq nat _ _ => prove_by_zify
                               | _ => idtac
                               end).
        }
        { (* padder is still running (count <= 15) *)
          destr (count <=? 15)%N; logical_simplify; subst;
          [ | destr (count =? 16)%N; logical_simplify; subst;
              exfalso; prove_by_zify ].

          all: repeat
              (repeat lazymatch goal with
                       | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                       | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                        end;
               try reflexivity;
               (destruct_one_match_hyp; logical_simplify; subst; try lia)).

          all:repeat destruct_one_match; logical_simplify; subst; try lia.
          all:try reflexivity.
          all:try prove_by_zify.
          all:rewrite firstn_padded_msg_truncate by prove_by_zify.
          all:reflexivity. } } } }

  Optimize Proof.
  { (* length block = 16 *)
    fold denote_type; change (denote_type sha_word) with N.
    repeat destruct_one_match.
    all:cbn [N.leb Pos.compare N.compare fst snd] in *.
    all:logical_simplify; subst; boolsimpl.
    all:repeat destruct_one_match; length_hammer. }
  { (* count <= 17 *)
    repeat destruct_one_match.
    all:cbn [N.leb Pos.compare N.compare fst snd] in *.
    all:logical_simplify; subst; boolsimpl.
    all:try lia.
    all:boolsimpl_hyps; N.bool_to_prop.
    all:compute_expr (2 ^ N.of_nat 6)%N.
    all:rewrite ?N.mod_small by lia.
    all:lia. }
  { (* padder_byte_index mod 4 = 0 *)
    repeat destruct_one_match; try reflexivity.
    all:try assumption.
    all:prove_by_zify. }

  { (* big if cleared then ... else ... clause *)
    compute_expr (2 ^ N.of_nat 6)%N.
    destr clear; [ ssplit; reflexivity | ].
    destr cleared; logical_simplify; subst.

    { (* cleared=true *)
      cbn [N.leb Pos.compare N.compare fst snd] in *.
      logical_simplify; subst.
      (* if data isn't valid, we stay cleared *)
      destr fifo_data_valid; logical_simplify; subst; boolsimpl;
        [ | ssplit; reflexivity ].
      natsimpl.
      rewrite !Nat.mod_small, !N.mod_small by lia.
      rewrite !Nat.div_small by lia.
      ssplit; try lia.
      all:repeat lazymatch goal with
                 | |- context [N.leb ?x ?y] => destr (N.leb x y); try lia
                 | |- context [N.ltb ?x ?y] => destr (N.ltb x y); try lia
                 end.
      all:try reflexivity.
      all:ssplit; try lia.
      all:repeat destruct_one_match; logical_simplify; subst; try lia.
      all:lazymatch goal with
          | |- context [length (new_msg_bytes _ _ _ _)] => cbv [new_msg_bytes]; length_hammer
          | _ => idtac
          end.
      (* should be only one case left, expression for block *)
      compute_expr (N.to_nat (0 + 1)). natsimpl.
      rewrite skipn_tl.
      (* simplify implicit types *)
      fold denote_type. change (denote_type sha_word) with N.
      push_skipn; listsimpl.
      rewrite slice_map_nth; cbn [List.map seq].
      reflexivity. }

    Optimize Proof.
    { (* cleared = false *)
      rewrite ?Tauto.if_same.
      (* destruct cases for [count] *)
      destr (count <=? 15)%N;
        [ destr (count =? 0)%N | destr (count =? 16)%N ];
        logical_simplify; subst; cbn [fst snd] in *.

      { idtac "subgoal 1: count=0 (transition from inner to padder".
        destr (padder_byte_index =? padder_byte_index / 64 * 64);
          [ | exfalso; prove_by_zify ].
        compute_expr ((0 + 1) mod 64)%N.
        repeat (natsimpl || boolsimpl || cbn [Nat.eqb N.eqb Pos.eqb]).
        ssplit.


        { (* padder_byte_index <= padded_message_size msg *)
          repeat destruct_one_match; logical_simplify; subst; lia. }
        { (* padder_byte_index <= padded_message_size msg *)
          repeat destruct_one_match; logical_simplify; subst; try lia;
          prove_by_zify. }
        { (* t <= 64 *)
          repeat destruct_one_match; logical_simplify; subst; lia. }
        { (* ready = (count <? 16)%N *)
          repeat destruct_one_match; logical_simplify; subst;
          repeat lazymatch goal with
                 | |- context [N.leb ?x ?y] => destr (N.leb x y); try lia
                 | |- context [N.ltb ?x ?y] => destr (N.ltb x y); try lia
                 end. }
        { (* digest = fold_left (SHA256.sha256_step msg)
                                (seq 0 completed_block_index) SHA256.H0 *)
          all: repeat
              (repeat lazymatch goal with
                       | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                       | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                        end;
               try reflexivity;
               (destruct_one_match_hyp; logical_simplify; subst; try lia)).

          all: boolsimpl.
          all: repeat lazymatch goal with
                 | |- context [N.leb ?x ?y] => destr (N.leb x y); try lia
                 | |- context [N.ltb ?x ?y] => destr (N.ltb x y); try lia
                 end.
          all:lazymatch goal with
              | H : ?x = ?x / ?y * ?y |- context [(?x + ?z) / ?y] =>
                rewrite H; rewrite (Nat.div_add_l (x / y) y) by lia;
                  rewrite ?Nat.div_small by lia; rewrite <-?H
              end.
          all:natsimpl; try reflexivity.

          all:lazymatch goal with
              | |- fold_left _ _ _ = fold_left _ _ _ =>
                eapply fold_left_ext_In; intros *;
                  rewrite in_seq; intros
              end.
          all:rewrite sha256_step_truncate by prove_by_zify.
          all:reflexivity. }
        { (* (if msg_complete
             then length msg <= padder_byte_index
             else padder_byte_index = length msg) *)
          repeat (destruct_one_match; logical_simplify; subst; try lia);
          cbv [new_msg_bytes]; length_hammer. }
        { (* (if done then ...  else True) *)
          repeat
              (repeat lazymatch goal with
                       | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                       | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                        end;
               try reflexivity;
               (destruct_one_match_hyp; logical_simplify; subst; try lia)).
          all: boolsimpl; ssplit; try lia.
          all: prove_by_zify.
          }
        { (* clause that depends on count; in this case next count will always be <= 15 *)

          repeat
              (repeat lazymatch goal with
                       | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                       | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                       | |- context [N.leb ?x ?y] => destr (N.leb x y); try lia
                        end;
               try reflexivity;
               (destruct_one_match_hyp; logical_simplify; subst; try lia)).

          all: ssplit; try lia.
          all: try abstract prove_by_zify.
          all:
              match goal with
               | H: skipn ?X _ = _ |- skipn ?X _ = _ => rewrite H
               | |- skipn ?X _ = _ => compute_expr X
               end.
          all: try reflexivity.

          all:rewrite ?tl_app by (intro; subst; cbn [length] in *; discriminate).
          all:fold denote_type.
          all:compute_expr (N.to_nat 1).
          all:change (denote_type sha_word) with N.
          all:push_skipn; push_length.
          all:push_skipn; listsimpl.

          all:rewrite slice_map_nth; cbn [seq List.map].
          all:repeat (f_equal; lazymatch goal with
                               | |- @eq nat _ _ => prove_by_zify
                               | _ => idtac
                               end). }
        }

        { idtac "subgoal 2: 0 < count <= 15 (padder running)".
          destr (17 =? count)%N; [lia|].
          destr (16 =? count)%N; [lia|].


          destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
            try discriminate; boolsimpl.
          all:rewrite ?Tauto.if_same in *; cbn [Nat.eqb].
          all: match goal with
               | |- context [( ?X mod ?Y )%N] => rewrite (N.mod_small X Y) by lia
               | |- _ => idtac
               end.
          (* { *)
            all: repeat lazymatch goal with
                     | |- context [Nat.eqb ?x ?y] => destr (Nat.eqb x y); try lia
                     | |- context [Nat.ltb ?x ?y] => destr (Nat.ltb x y); try lia
                     | |- context [N.ltb ?x ?y] => destr (N.ltb x y); try lia
                     | |- context [N.leb ?x ?y] => destr (N.leb x y); try lia
                      end.
            all: try (exfalso; prove_by_zify).

            (* all: repeat (destruct_one_match; logical_simplify; subst; try lia). *)


            all: autorewrite with Nnat.
            all:try match goal with
                | |- context [(?x + 4) / ?y] =>
                  replace ((x + 4)/y) with (x/y) by prove_by_zify
                | |- context [(?x + 4)/ ?y - 1] =>
                  replace ((x + 4)/y - 1) with (x/y) by prove_by_zify
                end.
            all: natsimpl.
            all: destr (Datatypes.length msg <? 64); try (exfalso; lia).
            all: try (destr (padder_byte_index <? 64); try lia).
            all: try (destruct done; try lia; try prove_by_zify).

            all: repeat destruct_one_match.
            all: ssplit;
              first
              [ reflexivity
              | lia
              | cbn [new_msg_bytes]; push_length; lia
              | prove_by_zify
              | idtac
              ].
            all: cbn [sha_word].
            all: lazymatch goal with
                 | H: skipn _ _ = _ |- context [skipn _ _ ] =>
                    rewrite ?skipn_tl; rewrite ?skipn_app;
                    replace (S (16 - (N.to_nat count + 1))) with (16 - N.to_nat count) by prove_by_zify;
                    rewrite H
                 | |- _ => idtac
                 end.

            all: replace (16 - N.to_nat count - Datatypes.length block) with 0 by lia.
            all: rewrite ?skipn_O.
            all: replace (N.to_nat count + 1) with (S (N.to_nat count)) by lia.
            all: subst.
            all: repeat destruct_one_match.
            all: try lazymatch goal with
                 | |- fold_left _ _ _ = fold_left _ _ _ =>
                    eapply fold_left_ext_In; intros *; rewrite in_seq; intros
                 end.

            all: try (
              rewrite <-slice_snoc; rewrite slicen_padded_msg_truncate by lia;
              f_equal; f_equal;
              rewrite ?nth_padded_msg;
              cbv [SHA256.padded_msg_bytes];
              rewrite <-!app_assoc; push_nth;
              reflexivity
              ).

            all: try (rewrite sha256_step_truncate; [reflexivity|prove_by_zify]).
            all: try reflexivity.
            all: try (
              replace ((padder_byte_index + 4 - 4)/ 4)
                with (padder_byte_index / 64 * 16 + N.to_nat count) by prove_by_zify).
            all: try (
              replace ((length msg + 4 - 4)/ 4)
                with (length msg / 64 * 16 + N.to_nat count) by prove_by_zify).
            all: try now rewrite slice_snoc.

            all: try (
              rewrite <- slice_snoc;
              f_equal;
              now rewrite slicen_padded_msg_truncate by prove_by_zify).

            all:
                assert (count = 15)%N by prove_by_zify;
                replace (16 - N.to_nat count) with 1 in * by lia;
                rewrite skipn_1 in H24;
                rewrite tl_app by (destruct block; cbn [length] in H5; [lia|congruence]);
                rewrite H24.
            all:
                try (
                match goal with
                | |- context[ new_msg_bytes _ _ ?T _ ] =>
                rewrite <- slicen_padded_msg_truncate with (msg2:=
                  (new_msg_bytes true fifo_data T final_length)) by prove_by_zify
                end).
            all: try rewrite slice_snoc.
            all:
                f_equal; prove_by_zify;
                reflexivity.
        }
        { idtac "subgoal 3".
          abstract (
          destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
            try discriminate; boolsimpl;
          rewrite ?Tauto.if_same in *; cbn [Nat.eqb];
          repeat (destruct_one_match; logical_simplify; subst; try lia);
          ssplit; try reflexivity; try lia; try prove_by_zify).
        }
        { idtac "subgoal 4".
          destr fifo_data_valid; destr msg_complete; logical_simplify; subst;
            try discriminate; boolsimpl;
          rewrite ?Tauto.if_same in *; cbn [Nat.eqb];
          repeat (destruct_one_match; logical_simplify; subst; try lia);
          destr(17 =? count)%N; try lia;
          try destr (padder_byte_index =? 0); try lia;
          try destr (t =? 63); try lia;
          destr (count =? 0)%N; try lia;
          ssplit; try reflexivity; try lia; try prove_by_zify;
          try match goal with
               | |- false = ?X => destr X; lia
              end;
          replace (16 - N.to_nat 0) with 16 by lia;
          try rewrite Tauto.if_same in E4; try lia;
          try (destr (length msg =? 0); lia);
          try rewrite skipn_all2 by lia; try reflexivity.
          all: destr (length msg =? 0); try lia.
          all: rewrite H29.
          all: rewrite fold_left_sha256_step_alt_firstn.
          all: try replace ( S (padder_byte_index / 64 - 1) ) with (padder_byte_index / 64) in * by prove_by_zify.
          all: try replace ( S (length msg / 64 - 1) ) with (length msg / 64) in * by prove_by_zify.
          all: try reflexivity.
          all:
            rewrite <- fold_left_sha256_step_alt_firstn' by lia;
            rewrite <- fold_left_sha256_step_alt_firstn' by lia;
            reflexivity.
        }
      }
    }
Time Qed.

Lemma sha256_output_correct : output_correct sha256.
Proof.
  simplify_invariant sha256. cbn [absorb_any].
  simplify_spec sha256.
  (* The following gymnastics results in input_, state_, and repr_ being posed
     as let-hypotheses, which makes proof debugging easier because one can look
     at them and see what case the proof is dealing with *)
  intros input state repr.
  pose (input_:=input). pose (state_:=state). pose (repr_:=repr).
  revert dependent repr. revert dependent state. revert dependent input.
  intros (fifo_data_valid,
          (fifo_data, (is_final, (final_length, (clear, []))))).
  intro.
  intros ((ready, (block, (digest, (count, done)))),
          (sha256_padder_state, sha256_inner_state)).
  intro.
  intros (((((msg, msg_complete), padder_byte_index), inner_byte_index), t), cleared).
  intros; logical_simplify; subst.

  rewrite step_sha256_simplified_eq. cbv [step_sha256_simplified]. cbn [fst snd].

  (* A whole bunch of assertions about the properties of padded_message_size
     related to all 3 possible next messages *)
  pose proof padded_message_size_mono
       msg (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_bytes_longer_than_input msg.
  pose proof padded_message_bytes_longer_than_input
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_bytes_longer_than_input
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof min_padded_message_size msg.
  pose proof min_padded_message_size
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof min_padded_message_size
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_size_modulo msg.
  pose proof padded_message_size_modulo
       (new_msg_bytes fifo_data_valid fifo_data is_final final_length).
  pose proof padded_message_size_modulo
       (msg ++ new_msg_bytes fifo_data_valid fifo_data is_final final_length).

  lazymatch goal with
  | H : sha256_padder_invariant ?state ?repr
    |- context [step sha256_padder ?state ?input] =>
    assert (precondition sha256_padder input repr)
  end.
  { simplify_spec sha256_padder; cbn [reset_repr sha256_padder_specification];
    destr cleared; logical_simplify; subst;
      [ destr fifo_data_valid; destr is_final; logical_simplify; subst;
        ssplit; solve [auto] | ];
    ssplit; [ assumption | ];
    destr fifo_data_valid; logical_simplify; subst; [ | tauto ];
    destr is_final; logical_simplify; subst; try tauto.
    all: ssplit; try tauto.
    all: destruct msg_complete; lia.
  }

  use_correctness' sha256_padder.
  cbn [reset_repr sha256_padder_specification] in *.

  (* prove that inner precondition is satisfied *)
  lazymatch goal with
  | H : sha256_inner_invariant ?state ?repr
    |- context [step sha256_inner ?state ?input] =>
    assert (precondition sha256_inner input repr)
  end.
  {
    abstract (
    simplify_spec sha256_inner; cbn [reset_repr sha256_inner_specification];
    destr cleared; logical_simplify; subst;
      [ destr fifo_data_valid; destr is_final; logical_simplify; subst;
        ssplit; solve [auto] | ];
    rewrite fold_left_sha256_step_alt_firstn;
    destr (t =? 64); logical_simplify; subst; try lia;
    destr (count <=? 15)%N; logical_simplify; subst;
    destr (count =? 16)%N; logical_simplify; subst; try lia;
    repeat (destruct_one_match; logical_simplify; subst; try lia);
    repeat lazymatch goal with
               | H : (Nat.eqb ?x ?y) = false |- _ => apply Nat.eqb_neq in H
           end;
    try (destr (padder_byte_index <? 64); logical_simplify; subst; [ | lia ]);
    rewrite ?Nat.div_mul, ?Nat.div_small in * by lia;
    try reflexivity;
    try discriminate;
    natsimpl;
    repeat lazymatch goal with
               | |- context [(?x + ?y) / ?y] => replace ((x + y) / y) with (x / y + 1) by prove_by_zify
               | |- context [S (?x - 1)] => replace (S (x - 1)) with x by prove_by_zify
           end;
    natsimpl;
    try (destr (inner_byte_index + 64 =? 64); logical_simplify; subst; lia);
    lazymatch goal with
        | |- _ /\ _ /\ _ => ssplit; [ reflexivity | | length_hammer ]
        | _ => idtac
    end;
    rewrite ?firstn_slice_app by (push_length; prove_by_zify);
    lazymatch goal with
        | |- fold_left _ _ _ = fold_left _ _ _ =>
          eapply fold_left_ext_In; intros *;
            rewrite in_seq; intros;
              rewrite !sha256_step_alt_firstn by lia;
              try reflexivity
        end).
  }

  use_correctness' sha256_inner.
  cbn [reset_repr sha256_inner_specification] in *.

  do 3 eexists; ssplit.
  { reflexivity. }
  { abstract(
    destruct clear; [reflexivity|]; logical_simplify; subst;
    destruct cleared; logical_simplify; subst; cbn [fst snd];
    destr (0 <=? 15)%N; destr (16 =? 0)%N; destr (0 =? 0)%N; try lia; boolsimpl; logical_simplify;
      subst; [ destruct fifo_data_valid; boolsimpl; reflexivity| ];
    destr (count <=? 15)%N; destr (16 =? count)%N; try lia; boolsimpl; logical_simplify; subst;
      repeat (destruct_one_match; logical_simplify; subst; try lia); boolsimpl;

      repeat (match goal with
                  | |- context [ ?X =? ?Y ] => destr ( X =? Y); try lia
                  | |- context [ ?X <=? ?Y ] => destr ( X <=? Y); try lia
                  | |- context [ ( ?X =? ?Y )%N ] => destr ( X =? Y)%N; try lia
                  | |- context [ ( ?X <=? ?Y )%N ] => destr ( X <=? Y)%N; try lia
                  end; boolsimpl);
      try lia;
      repeat (destruct_one_match_hyp; logical_simplify; subst; try lia);
      try lia; try prove_by_zify
    ).
  }

  {
    abstract (
    destruct clear; [reflexivity|]; logical_simplify; subst;
    destruct cleared; logical_simplify; subst; cbn [fst snd];
    destr (0 <=? 15)%N; destr (16 =? 0)%N; destr (0 =? 0)%N; try lia; boolsimpl; logical_simplify; subst;
    [ destruct fifo_data_valid; boolsimpl; reflexivity |];
    rewrite N.mod_small by (cbn; prove_by_zify);
    destr (count <=? 15)%N; try lia; boolsimpl; logical_simplify; subst;
    destr (16 =? count)%N; try lia; boolsimpl; logical_simplify; subst;
    repeat (destruct_one_match; logical_simplify; subst; try lia);
    boolsimpl;

    repeat (match goal with
                | |- context [ ?X =? ?Y ] => destr ( X =? Y); try lia
                | |- context [ ?X <=? ?Y ] => destr ( X <=? Y); try lia
                | |- context [ ( ?X =? ?Y )%N ] => destr ( X =? Y)%N; try lia
                | |- context [ ( ?X <=? ?Y )%N ] => destr ( X <=? Y)%N; try lia
                end; boolsimpl); try prove_by_zify;

    repeat (match goal with
                | H: context [ ?X =? ?Y ] |- _ => destr ( X =? Y); try lia
                | H: context [ ?X <=? ?Y ] |- _ => destr ( X <=? Y); try lia
                | H: context [ ( ?X =? ?Y )%N ] |- _ => destr ( X =? Y)%N; try lia
                | H: context [ ( ?X <=? ?Y )%N ] |- _ => destr ( X <=? Y)%N; try lia
                end; boolsimpl);
    try lia; try prove_by_zify;
    repeat (destruct_one_match_hyp; logical_simplify; subst; try lia);
    try lia; try prove_by_zify).
  }

  destruct clear; [abstract reflexivity|]; logical_simplify; subst.
  destruct cleared; logical_simplify; subst; cbn [fst snd];
  destruct fifo_data_valid; boolsimpl; cbn [fst snd]; [abstract reflexivity .. | ].
  destruct_one_match;[|abstract reflexivity].

  Optimize Proof.
  cbv [SHA256.sha256 SHA256.w]; replace (512 / N.to_nat 32) with 16 by (abstract prove_by_zify);
  rewrite concat_digest_to_N_id; rewrite padded_message_length; cycle 1.
  { Time abstract (cbv [SHA256.sha256_step];

    assert (seq 0 (padded_message_size msg / 4 / 16) <> []);
    [ assert (1 <= padded_message_size msg / 4 / 16) by prove_by_zify;
      apply length_pos_nonnil;
      length_hammer
 |];

    pose proof (fold_left_exists_final (fun (H0 : list N) (i : nat) =>
      List.map2 SHA256.add_mod H0
        (fold_left (SHA256.sha256_compress (SHA256.W msg i)) (seq 0 64) H0))
        (seq 0 (padded_message_size msg / 4 / 16)) SHA256.H0 H19) as Hff;
    logical_simplify;
    rewrite H21;

    remember (fold_left (SHA256.sha256_compress (SHA256.W msg x4)) (seq 0 64) x3) as X;
    clear;

    rename x3 into a;
    rename X into b;

    rewrite map2_resize with (d := 0%N);
    cbn zeta;

    apply Forall2_implies_Forall_map2;
    revert a;
    induction b;
    [ intros; destruct a; now cbn|];
    intros;
    destruct a0;[now cbn|];
    push_length;
    rewrite <- Min.succ_min_distr;
    cbn zeta;
    rewrite ? resize_cons;
    constructor;
    [ apply sha256_add_mod_bounded|];
    apply IHb).
  }
  { abstract (apply fold_left_sha256_step_length; reflexivity).  }

  destruct_one_match.
  { abstract (
    destr (inner_byte_index =? 0);
    [
      repeat (match goal with
                  | H: context [ ?X =? ?Y ] |- _ => destr ( X =? Y); try lia
                  | H: context [ ?X <=? ?Y ] |- _ => destr ( X <=? Y); try lia
                  | H: context [ ( ?X =? ?Y )%N ] |- _ => destr ( X =? Y)%N; try lia
                  | H: context [ ( ?X <=? ?Y )%N ] |- _ => destr ( X <=? Y)%N; try lia
                  end; boolsimpl)|
                    ];
    destr (16 =? count)%N; try prove_by_zify;
    destr (if if t =? 64 then true else false then true else t =? 63); [|prove_by_zify];
    destr done; destr (count <=? 15)%N; destr (count =? 16)%N; logical_simplify; subst; try prove_by_zify;

    repeat (match goal with
                  | H: context [ ?X =? ?Y ] |- _ => destr ( X =? Y); try lia
                  | H: context [ ?X <=? ?Y ] |- _ => destr ( X <=? Y); try lia
                  | H: context [ ( ?X =? ?Y )%N ] |- _ => destr ( X =? Y)%N; try lia
                  | H: context [ ( ?X <=? ?Y )%N ] |- _ => destr ( X <=? Y)%N; try lia
                  end; boolsimpl); try prove_by_zify).
  }
  all: repeat (match goal with
              | H: context [ ?X =? ?Y ] |- _ => destr ( X =? Y); try lia
              | H: context [ ?X <=? ?Y ] |- _ => destr ( X <=? Y); try lia
              | H: context [ ( ?X =? ?Y )%N ] |- _ => destr ( X =? Y)%N; try lia
              | H: context [ ( ?X <=? ?Y )%N ] |- _ => destr ( X <=? Y)%N; try lia
              end; boolsimpl); try prove_by_zify.
  all: logical_simplify; subst.
  { rewrite <- E4. reflexivity. }
  do 2 f_equal.
  prove_by_zify.
Qed.

Existing Instances sha256_invariant_preserved sha256_output_correct sha256_invariant_at_reset.

Global Instance sha256_correctness : correctness_for sha256.
Proof. constructor; try typeclasses eauto. Defined.

