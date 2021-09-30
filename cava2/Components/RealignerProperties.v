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
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Require Import coqutil.Tactics.Tactics.

Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Byte.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.If.

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.Components.Realigner.

Import ListNotations.

Local Open Scope bool.
Local Open Scope nat.
Local Open Scope list.

Section RealignerSpec.
  Local Open Scope N.

  Lemma mask_1000 x:
    x < 2 ^ 32 -> N.land x 0xFF000000 = N.shiftl (N.shiftr x 24) 24.
  Proof.
    clear. intros.
    apply N.bits_inj.
    cbv [N.eqf]; intros.
    rewrite N.land_spec.

    replace n with (N.of_nat (N.to_nat n)) by now rewrite N2Nat.id.
    remember (N.to_nat n) as n'.
    clear Heqn' n.

    destr (n' <? 32)%nat.
    { do 32 (destruct n'; [push_Ntestbit; now boolsimpl| ]); lia. }
    {
      push_Ntestbit; boolsimpl.
      rewrite N.sub_add by lia.
      repeat rewrite (N.testbit_high_lt _ _ _ H) by lia.
      now boolsimpl.
    }
  Qed.

  Lemma mask_1100 x:
    x < 2 ^ 32 -> N.land x 0xFFFF0000 = N.shiftl (N.shiftr x 16) 16.
  Proof.
    clear. intros.
    apply N.bits_inj.
    cbv [N.eqf]; intros.
    rewrite N.land_spec.

    replace n with (N.of_nat (N.to_nat n)) by now rewrite N2Nat.id.
    remember (N.to_nat n) as n'.
    clear Heqn' n.

    destr (n' <? 32)%nat.
    { do 32 (destruct n'; [push_Ntestbit; now boolsimpl| ]); lia. }
    {
      push_Ntestbit; boolsimpl.
      rewrite N.sub_add by lia.
      repeat rewrite (N.testbit_high_lt _ _ _ H) by lia.
      now boolsimpl.
    }
  Qed.

  Lemma mask_1110 x:
    x < 2 ^ 32 -> N.land x 0xFFFFFF00 = N.shiftl (N.shiftr x 8) 8.
  Proof.
    clear. intros.
    apply N.bits_inj.
    cbv [N.eqf]; intros.
    rewrite N.land_spec.

    replace n with (N.of_nat (N.to_nat n)) by now rewrite N2Nat.id.
    remember (N.to_nat n) as n'.
    clear Heqn' n.

    destr (n' <? 32)%nat.
    { do 32 (destruct n'; [push_Ntestbit; now boolsimpl| ]); lia. }
    {
      push_Ntestbit; boolsimpl.
      rewrite N.sub_add by lia.
      repeat rewrite (N.testbit_high_lt _ _ _ H) by lia.
      now boolsimpl.
    }
  Qed.

  Lemma fold_left_4_byte_suffix x xs:
    (length xs = 4)%nat ->
    exists e: {X:N | X < 2 ^ 32},
    (fold_left
       (fun (acc : N) (b3 : Byte.byte) => N.lor (N.shiftl acc 8) (Byte.to_N b3))
       xs x)
    = N.lor (N.shiftl x 32) (proj1_sig e).
  Proof.
    intros.
    destruct xs; [easy|].
    destruct xs; [easy|].
    destruct xs; [easy|].
    destruct xs; [easy|].
    destruct xs; [|easy].
    eexists (x:= exist (fun n => n < 2 ^ 32)
       (N.lor
       (N.lor
          (N.lor (N.shiftl (N.shiftl (N.shiftl (Byte.to_N b) 8) 8) 8)
             (N.shiftl (N.shiftl (Byte.to_N b0) 8) 8))
          (N.shiftl (Byte.to_N b1) 8)) (Byte.to_N b2))
        _
    ).
    cbn.
    intros.
    apply N.bits_inj; cbv [N.eqf]; intros.
    push_Ntestbit.
    destr (n <? 32).
    { rewrite N.shiftl_spec_low with (n:=32) by lia.
      destr (n <? 8).
      { push_Ntestbit. shelve. }
      { push_Ntestbit.
        destr (n <? 16).
        { rewrite N.shiftl_spec_low.
          { shelve. }
          { lia. }
        }
        push_Ntestbit.
        destr (n <? 24).
        { rewrite N.shiftl_spec_low.
          { shelve. }
          { lia. }
        }
        push_Ntestbit.
        repeat rewrite Bool.orb_false_l.
        repeat rewrite <- N.shiftl_spec_high by lia.
        repeat rewrite <- N.lor_spec.
        reflexivity.
      }
    }
    push_Ntestbit.
    repeat rewrite testbit_byte by lia.
    repeat rewrite <- N.sub_add_distr.
    repeat rewrite Bool.orb_false_r.
    cbn.
    reflexivity.

    Unshelve.
    { repeat rewrite N.shiftl_shiftl.
      cbn.
      change 4294967296 with (2^32).

      repeat (
        change (2^32) with (N.max (2^32) (2^32));
        apply N.lor_lt);
        try rewrite N.shiftl_mul_pow2.

        { apply (N.lt_le_trans _ (2 ^ 8 * 2 ^ 24)); try (cbn; lia).
          { apply N.mul_lt_mono_pos_r. { now cbn. }
            cbn.
            pose (Byte.to_N_bounded b).
            lia.
          }
        }
        { apply (N.lt_le_trans _ (2 ^ 8 * 2 ^ 16)); try (cbn; lia).
          { apply N.mul_lt_mono_pos_r. { now cbn. }
            cbn.
            pose (Byte.to_N_bounded b0).
            lia.
          }
        }
        { apply (N.lt_le_trans _ (2 ^ 8 * 2 ^ 8)); try (cbn; lia).
          { apply N.mul_lt_mono_pos_r. { now cbn. }
            cbn.
            pose (Byte.to_N_bounded b1).
            lia.
          }
        }
        pose (Byte.to_N_bounded b2).
        cbn; lia.
    }

    all: push_Ntestbit;
         repeat rewrite Bool.orb_false_l; reflexivity.
  Qed.

  Lemma shiftr_concat_bytes_4 (x: list Byte.byte):
    (length x < 8)%nat ->
    N.shiftr (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 x)) (N.of_nat 32) =
    BigEndianBytes.concat_bytes (List.resize Byte.x00 4 x).
  Proof.
    cbv [BigEndianBytes.concat_bytes].
    intros.
    Ltac t :=
      cbn -[N.shiftr ];
      repeat rewrite N.lor_0_r;
      repeat rewrite N.shiftl_shiftl;
      try rewrite N.shiftr_shiftl_l by lia;
      try rewrite N.shiftl_0_r;
      try now cbn.
    destruct x; [t|
    destruct x; [t|
    destruct x; [t|
    destruct x; [t|]]]].

    repeat rewrite resize_cons.
    cbn [fold_left].
    pose (fold_left_4_byte_suffix
       (N.lor
          (N.shiftl
             (N.lor
                (N.shiftl
                   (N.lor (N.shiftl (N.lor (N.shiftl 0 8) (Byte.to_N b)) 8)
                      (Byte.to_N b0)) 8) (Byte.to_N b1)) 8)
          (Byte.to_N b2))
        (List.resize Byte.x00 4 x)
    ).
    destruct e.
    { apply resize_length. }
    rewrite H0.
    cbn -[N.shiftr].
    rewrite N.shiftr_lor.
    rewrite N.shiftr_shiftl_l by lia.
    assert (N.shiftr (@proj1_sig N (fun X : N => (X < 4294967296)%N) x0) 32 = 0%N).
    { rewrite N.shiftr_eq_0; [reflexivity|].
      destruct x0.
      cbn [proj1_sig].
      destr (x0 =? 0)%N.
      { rewrite E. now cbn. }
      apply N.log2_lt_pow2.
      { lia. }
      apply l.
    }
    rewrite H1.
    rewrite N.lor_0_r.
    rewrite N.shiftl_0_r.
    reflexivity.
  Qed.

  Definition realign_inner_spec
    (existing: list Byte.byte) data data_mask := (
      let '(a,b,c,d) :=
        match BigEndianBytes.N_to_bytes 4 data with
        | a::b::c::d::_ => (a,b,c,d)
        | _ => (Byte.x00,Byte.x00,Byte.x00,Byte.x00)
        end in
      existing ++
           if data_mask =? 0x0 then []
      else if data_mask =? 0x1 then [d]
      else if data_mask =? 0x2 then [c]
      else if data_mask =? 0x4 then [b]
      else if data_mask =? 0x8 then [a]
      else if data_mask =? 0x3 then [c;d]
      else if data_mask =? 0x6 then [b;c]
      else if data_mask =? 0xC then [a;b]
      else if data_mask =? 0x9 then [b;c;d]
      else if data_mask =? 0xE then [a;b;c]
      else [a;b;c;d]
      )%N.

  Definition realign_inner_pre
    existing'
    (input : denote_type (input_of (realign_inner (var:=denote_type) )))
    :=
    let '(existing, (existing_len, (data, (data_mask, tt)))) := input in
    existing < 2 ^ 32 /\
    existing_len < 4 /\
    data < 2 ^ 32 /\
    existing' = (firstn (N.to_nat existing_len) (BigEndianBytes.N_to_bytes 4 existing)).

  Lemma step_realign_inner
    existing'
    (input : denote_type (input_of (realign_inner (var:=denote_type) )))
    (state : denote_type (state_of (realign_inner (var:=denote_type) ))):
    realign_inner_pre existing' input ->
    step realign_inner state input =
    let aligned := realign_inner_spec existing' (fst (snd (snd input))) (fst (snd (snd (snd input)))) in
    (tt, (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 aligned), N.of_nat (length aligned))).
  Proof.
    destruct input as (existing, (existing_len, (input, (input_mask, [])))).
    cbn in state.
    cbv [realign_inner realign_inner_pre realign_inner_spec K bvconcat bvslice bvresize] in *;
      stepsimpl.
    repeat (destruct_pair_let; cbn[fst snd]).
    intros Hpre.
    destruct Hpre as [? [? [? ?]]].
    rewrite H2 in *.

    f_equal.

    cbv [BigEndianBytes.N_to_bytes seq List.map].

    cbn [Nat.add].
    repeat rewrite N.lor_0_r.
    repeat rewrite N.land_ones.

    do 4 rewrite mask_1000 by (try apply N.mod_upper_bound; lia).
    do 3 rewrite mask_1100 by (try apply N.mod_upper_bound; lia).
    do 2 rewrite mask_1110 by (try apply N.mod_upper_bound; lia).

    repeat
      match goal with
      | |- context [N.eqb existing_len ?X] =>
        let H := fresh in destruct (N.eqb_spec existing_len X) as [H|H]; try rewrite H
      | |- context [N.eqb input_mask ?X] =>
        let H := fresh in destruct (N.eqb_spec input_mask X) as [H|H]; try rewrite H
      end;
      try match goal with
      | _: ?X <> 0
      , _: ?X <> 1
      , _: ?X <> 2
      , _: ?X < 4
      |- _ =>
        let H := fresh in
        assert (X = 3) by lia; rewrite H
      end.

    all:
      f_equal;
      try rewrite app_nil_r;
      try rewrite length_app;
      try rewrite firstn_length;
      cbv [firstn N.to_nat Pos.to_nat Pos.iter_op Nat.add];
      cbv [BigEndianBytes.concat_bytes repeat List.resize fold_left List.app fst snd length Nat.sub Init.Nat.min N.of_nat firstn];
      repeat rewrite N2Byte.id;
      cbv [Byte.to_N];
      repeat rewrite N.lor_0_r;
      repeat rewrite N.shiftl_shiftl;
      repeat rewrite N.div2_spec;
      repeat rewrite N.shiftr_shiftr;
      cbn [fst snd Nat.add Nat.sub N.add Pos.add Pos.succ Pos.of_succ_nat].

    Ltac brute :=
      repeat (first
        [
          rewrite Bool.orb_false_l
        | rewrite Bool.orb_false_r
        | rewrite N.shiftl_spec_low by lia
        | rewrite N.mod_pow2_bits_low by lia
        | rewrite N.shiftl_spec_high by lia
        | rewrite N.mod_pow2_bits_high by lia
        | rewrite N.shiftr_spec by lia
        | rewrite N.shiftl_0_l by lia
        | rewrite N.shiftl_0_r by lia
        | rewrite N.lor_0_l by lia
        | rewrite N.lor_0_r by lia
        | rewrite N.shiftr_0_l by lia
        | rewrite N.shiftr_0_r by lia
        | rewrite N.lor_spec by lia
        ]);
        try reflexivity;
        try match goal with
            | |- N.testbit ?i ?X = N.testbit ?i ?Y => f_equal; lia
            end;
        try lia.

    all:
      apply N.bits_inj; cbv [N.eqf]; intros;

      change (0*8) with 0;
      change (256) with (2^8);

      destr (n <? 64); brute;
      destr (n <? 32); brute;
      destr (n <? 24); brute;
      destr (n <? 56); brute;
      destr (n <? 48); brute;
      destr (n <? 16); brute;
      destr (n <? 40); brute;
      destr (n <? 8); brute.

    all:
      rewrite N.testbit_high_lt with (x:=input) (n:=32) by lia;
      rewrite Bool.orb_false_r;
      match goal with
      | |- N.testbit ?i ?X = N.testbit ?i ?Y => f_equal; lia
      end.
  Qed.

  Definition realign_spec
    latched_valid
    latched_bytes
    state_data
    (input : denote_type (input_of (var:=denote_type) realign)) := (
    let '(_, (_, (_, (flush, (consumer_ready, tt))))) := input in

    if negb consumer_ready then
      (latched_valid, (BigEndianBytes.concat_bytes (List.resize Byte.x00 4 latched_bytes), N.of_nat (length latched_bytes)))
    else
      let out := firstn 4 state_data in
      let valid := 4 <=? length state_data in

      let valid_or_flushing := valid || (flush && (1 <=? length state_data)) in

      (valid_or_flushing, (BigEndianBytes.concat_bytes (List.resize Byte.x00 4 out), N.of_nat (length out))))%nat.

  Definition realign_update_state
    state_data
    (input : denote_type (input_of (var:=denote_type) realign)) := (
    let '(data_valid, (data, (data_mask, (flush, (consumer_ready, tt))))) := input in
    if negb consumer_ready then
      state_data
    else
      let state' :=
        if (4 <=? length state_data) || flush then
          skipn 4 state_data
        else state_data in

      if data_valid && negb flush then realign_inner_spec state' data data_mask else state')%nat.

  Definition realign_update_latched_bytes
    (latched_bytes: list Byte.byte)
    state_data
    (input : denote_type (input_of (var:=denote_type) realign))
    :=
    let '(data_valid, (data, (data_mask, (flush, (consumer_ready, tt))))) := input in
    if negb consumer_ready then
      latched_bytes
    else
      firstn 4 state_data.

  Definition realign_update_latched_valid
    (latched_valid: bool)
    (state_data: list Byte.byte)
    (input : denote_type (input_of (var:=denote_type) realign)) := (
    let '(data_valid, (data, (data_mask, (flush, (consumer_ready, tt))))) := input in
    if negb consumer_ready then
      latched_valid
    else
      (4 <=? length state_data) || flush && (1 <=? length state_data))%nat.

  Definition realign_pre
    (input : denote_type (input_of (var:=denote_type) realign))
    (state: denote_type (state_of (var:=denote_type) realign))
    :=
    let '(data_valid, (data, (data_mask, (flush, (consumer_ready, tt))))) := input in

    (data < 2 ^ 32)%N
    .

  Definition realign_invariant
    latched_valid latched_bytes
    (ghost_state: list Byte.byte)
    (state: denote_type (state_of (var:=denote_type) realign))
    :=
    let '(out_valid, (out_data, (out_len, (buff, buff_len)))) := state in

    buff_len = N.of_nat (length ghost_state)
    /\ out_valid = latched_valid
    /\ out_data = BigEndianBytes.concat_bytes (List.resize Byte.x00 4 latched_bytes)
    /\ N.to_nat out_len = length latched_bytes
    /\ buff = BigEndianBytes.concat_bytes (List.resize Byte.x00 8 ghost_state)
    /\ (buff < 2 ^ 64)%N
    /\ (buff_len < 8)%N
    .


  Lemma step_realign_invariant
    latched_valid latched_bytes state_data
    next_latched_valid next_latched_bytes next_state_data
      (input : denote_type (input_of (realign (var:=denote_type) )))
      (state : denote_type (state_of (realign (var:=denote_type) ))) :
    next_state_data = realign_update_state state_data input ->
    next_latched_bytes = realign_update_latched_bytes latched_bytes state_data input ->
    next_latched_valid = realign_update_latched_valid latched_valid state_data input ->
    realign_pre input state ->
    realign_invariant latched_valid latched_bytes state_data state ->
    realign_invariant next_latched_valid next_latched_bytes next_state_data (fst (step realign state input)).
  Proof.
    destruct input as (input_valid, (input_data, (input_mask, (flush, (consumer_ready, []))))).
    destruct state as (out_valid, (out_data, (out_length, (q, q_len)))).
    intros Hst Hlatch Hlatchvalid Hpre Hinv.
    destruct Hinv as [Hbuff_len [Hlatch_valid [Hlatch_bytes [Hlatch_bytes_len [Hfirst_bytes [Hbuf_bound Hbuf_len_bound]]]]]].
    cbv [realign realign_spec realign_pre realign_invariant realign_update_state realign_update_latched_bytes realign_update_latched_valid K] in *;
    stepsimpl.

    repeat (destruct_pair_let; cbn[fst snd]);
    autorewrite with tuple_if.
    erewrite step_realign_inner.

    2: {
      cbv [realign_inner_pre].
      split.
      { cbv [bvslice bvresize]; stepsimpl; cbn [fst snd].
        destruct ( (4 <=? q_len) || flush)%N;
        rewrite N.land_ones; replace (N.of_nat 32) with 32%N by lia;
        apply N.mod_lt; try lia.
      }
      split.
      { cbn [fst snd].
        destruct ( (4 <=? q_len) )%N eqn:?; boolsimpl.
        {
          replace (2^N.of_nat 4)%N with 16%N by now cbn.
          rewrite N.add_sub_swap by now apply N.leb_le.
          rewrite N.add_mod by lia.
          rewrite N.mod_same by lia.
          rewrite N.add_0_r.
          rewrite N.mod_mod by lia.

          rewrite N.mod_small.
          { apply (N.lt_le_trans _ (8 - 4)%N); lia. }
          lia.
        }
        apply N.leb_gt in Heqb.
        destruct flush; try lia.
      }
      split; [lia|]. reflexivity.
    }

    autorewrite with tuple_if.
    destr consumer_ready; cbn [negb fst snd] in *.
    2: {
      subst.
      rewrite Hlatch_bytes_len.
      tauto.
    }


    assert
      ((N.of_nat (Init.Nat.min
                  (N.to_nat
                     (if (4 <=? N.of_nat (length state_data)) || flush
                      then
                       if 4 <=? N.of_nat (length state_data)
                       then
                        (N.of_nat (length state_data) + 2 ^ N.of_nat 4 - 4)
                        mod 2 ^ N.of_nat 4
                       else 0
                      else N.of_nat (length state_data))) 4))%N
        =
            ((if (4 <=? length state_data)%nat || flush
              then N.of_nat (length state_data - 4)
              else N.of_nat (length state_data)) )%N)
              as Heq1.
    {  destr ((4 <=? N.of_nat (length state_data)));
       destr ((4 <=? length state_data))%nat;
       destruct flush; boolsimpl; try lia; rewrite Nat.min_l;
           rewrite N.add_sub_swap by apply E;
           rewrite N.add_mod by (now cbn);
           rewrite N.mod_same by (now cbn);
           rewrite N.add_0_r;
           rewrite N.mod_mod by (now cbn);
           rewrite N.mod_small; cbn; lia.
    }

    assert ((
            if (4 <=? N.of_nat (length state_data))%N || flush
            then
             if (4 <=? N.of_nat (length state_data))%N
             then
              ((N.of_nat (length state_data) + 2 ^ N.of_nat 4 - 4) mod 2 ^ N.of_nat 4)%N
             else 0%N
             else N.of_nat (length state_data)) =
            (
            if (4 <=? length state_data) || flush
            then N.of_nat (length state_data - 4)
            else N.of_nat (length state_data)))%nat as Heq2.
    {  destr ((4 <=? N.of_nat (length state_data)));
       destr ((4 <=? length state_data))%nat;
       destruct flush; boolsimpl; try lia;
           rewrite N.add_sub_swap by apply E;
           rewrite N.add_mod by (now cbn);
           rewrite N.mod_same by (now cbn);
           rewrite N.add_0_r;
           rewrite N.mod_mod by (now cbn);
           rewrite N.mod_small; cbn; lia.
    }

    ssplit.
    {
      subst; cbn [negb fst snd].
      autorewrite with tuple_if.
      cbv [realign_inner_spec].
      repeat rewrite unfold_N_to_bytes_4.
      push_length.
      repeat rewrite Nat2N.of_nat_if.
      repeat rewrite Nat2N.inj_add.
      repeat rewrite Nat2N.of_nat_if.
      rewrite Heq1.
      rewrite Heq2.

      reflexivity.
    }
    {
      subst;
      destr (1 <=? length state_data)%nat;
      destr (1 <=? N.of_nat (length state_data))%N;
      destr (4 <=? length state_data)%nat;
      destr (4 <=? N.of_nat (length state_data))%N;
      try lia; now boolsimpl.
    }
    { subst; cbv [bvslice bvresize]; stepsimpl; cbn [fst snd].
      rewrite N.land_ones_low.
      { rewrite resize_firstn by lia.
        now rewrite shiftr_concat_bytes_4 by lia.
      }

      apply (N.lt_le_trans _ (N.log2 (N.shiftr (2 ^ 64) (N.of_nat 32)))).
      { compute_expr (N.log2 (N.shiftr (2 ^ 64) (N.of_nat 32)))%N.
        destr (N.shiftr
          (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 state_data))
          (N.of_nat 32)).
        { cbn; lia. }
        apply N.log2_lt_pow2.
        { lia. }
        rewrite <- E.
        change (N.of_nat 32) with 32%N.
        replace (N.shiftr (BigEndianBytes.concat_bytes (List.resize Byte.x00 8 state_data)) 32)
          with ((BigEndianBytes.concat_bytes (List.resize Byte.x00 8 state_data)) / 2 ^ 32)%N
          by now rewrite N.shiftr_div_pow2.
        { apply N.div_lt_upper_bound.
          { lia. }
          { now change (2 ^ 32 * 2 ^ 32)%N with (2^64)%N. }
        }
      }
      now cbn.
    }
    { subst; cbv [bvmin bvslice bvresize]; stepsimpl; cbn [fst snd].
      rewrite apply_if_ext_1.
      repeat rewrite N.land_ones_low.
      {
        rewrite firstn_length.
        destr (N.of_nat (length state_data) <=? 4)%N;
        destr (length state_data <=? 4)%nat; try lia.
      }
      { now cbn. }
      { change 8%N with (2^3)%N in Hbuf_len_bound.
        apply (N.lt_trans _ 3).
        { destr ((0 =? N.of_nat (length state_data))%N).
          { now rewrite <- E. }
          { apply N.log2_lt_pow2;lia. }
        }
        lia.
      }
    }
    { cbv [bvslice bvresize]; stepsimpl; cbn [fst snd].
      subst.
      rewrite Heq2.
      autorewrite with tuple_if.
      cbn [fst snd].
      destruct (input_valid && negb flush).
      { do 3 f_equal.
        destr ( (4 <=? length state_data) )%nat;
        destr ( (4 <=? N.of_nat (length state_data)) )%N;
        try lia; boolsimpl.
        { rewrite N.shiftr_0_r.
          destruct state_data; [cbn in E; contradiction|].
          destruct state_data; [cbn in E; contradiction|].
          destruct state_data; [cbn in E; contradiction|].
          destruct state_data; [cbn in E; contradiction|].
          destruct state_data. { now cbn. }
          destruct state_data.

          Local Ltac bitify :=
            apply Byte2N.inj; rewrite N2Byte.id; apply N.bits_inj; cbv [N.eqf].

          Local Ltac s1 :=
            rewrite <- N.land_ones with (n:=8);
            replace 4294967295 with (N.ones 32) by now cbn;
            push_Ntestbit.
          Local Ltac s2 :=
              repeat (rewrite <- N.add_sub_assoc by lia; cbn);
              repeat rewrite N.add_0_r;
              repeat match goal with
                     | |- context [ N.testbit (Byte.to_N _ ) (?x + ?y)] =>
                      repeat rewrite testbit_byte with (n:= x + y) by lia; boolsimpl
                     end.
          Local Ltac s3 :=
            try reflexivity;
            try (now apply testbit_byte);
            try (symmetry; now apply testbit_byte).

          { cbn -[N.shiftr].
            replace (Pos.to_nat 1) with 1%nat by now cbn.
            rewrite firstn_cons.
            rewrite firstn_O.
            f_equal.
            bitify; intros; s1.
            destr (n <? 8);
              push_Ntestbit;
              boolsimpl; s2; s3.
          }

          destruct state_data.
          { cbn -[N.shiftr].
            replace (Pos.to_nat 2) with 2%nat by now cbn.
            repeat rewrite firstn_cons.
            rewrite firstn_O.
            f_equal; [|f_equal];
              bitify; intros; s1;
              destr (n <? 8);
                push_Ntestbit;
                boolsimpl; s2; s3.
          }
          destruct state_data.
          { cbn -[N.shiftr].
            replace (Pos.to_nat 3) with 3%nat by now cbn.
            repeat rewrite firstn_cons.
            rewrite firstn_O.
            f_equal; [|f_equal;[|f_equal]];
              bitify; intros; s1;
              destr (n <? 8);
                push_Ntestbit;
                boolsimpl; s2; s3.
          }
          cbn in Hbuf_len_bound.
          lia.
        }
        rewrite skipn_all2 by lia.
        destruct flush.
        { rewrite Nat2N.id.
          replace (length state_data - 4)%nat with 0%nat by lia.
          now rewrite firstn_O.
        }
        rewrite shiftr_concat_bytes_4 by lia.
        rewrite N.land_ones_low by (
            destr (BigEndianBytes.concat_bytes (List.resize Byte.x00 4 state_data) =? 0);
            try (rewrite E1; cbn; lia);
            rewrite <- N.log2_lt_pow2 by lia;
            now apply concat_bytes_4_bound).
        rewrite bytes_to_N_id_4 by now push_length.
        cbv [List.resize].
        rewrite Nat2N.id.
        push_firstn.
        now rewrite List.app_nil_r.
      }


      destr ( (4 <=? length state_data) )%nat;
      destr ( (4 <=? N.of_nat (length state_data)) )%N;
      try lia; boolsimpl;
      apply N.bits_inj; cbv [N.eqf]; intros; push_Ntestbit; boolsimpl.
      {
        destr (n <? 32); push_Ntestbit; boolsimpl.
        { rewrite <- concat_bytes_spec; now rewrite concat_bytes_skip_4_of_8_spec by lia. }
        destr (n <? 64); push_Ntestbit; boolsimpl.
        {
          replace (n - N.of_nat 32 + N.of_nat 0) with (n - 32) by lia.
          repeat rewrite <- concat_bytes_spec.
          now rewrite concat_bytes_skip_lower32 by lia.
        }
        repeat rewrite <- concat_bytes_spec.
        now rewrite concat_bytes_8_is_64bit by lia.
      }
      {
        destr (n <? 32); push_Ntestbit; boolsimpl.
        {
          destruct flush; repeat rewrite <- concat_bytes_spec.
          { now rewrite concat_bytes_skip_4_of_8_spec by lia. }
          { now rewrite concat_bytes_lower_8_zero by lia. }
        }
        destruct flush;
        destr (n <? 64); push_Ntestbit; boolsimpl;
        replace (n - N.of_nat 32 + N.of_nat 0) with (n - 32) by lia;
        repeat rewrite <- concat_bytes_spec.
        { now rewrite concat_bytes_skip_lower32 by lia. }
        { now rewrite concat_bytes_8_is_64bit. }
        { now replace (n - N.of_nat 32 + N.of_nat 32) with n by lia. }
        now rewrite concat_bytes_8_is_64bit.
      }
    }
    { cbv [bvslice bvresize]; subst; stepsimpl;
      rewrite Heq2;
      autorewrite with tuple_if;
      cbn [fst snd].
      destruct (input_valid && negb flush).
      { apply concat_bytes_8_bound. }
      rewrite N.land_0_l.
      rewrite N.shiftr_0_r.
      apply (N.lt_le_trans _ (N.max (2^64) (2^64))).
      2:{ lia. }
      apply N.lor_lt with (xs:=64) (ys:=64).
      2:{ lia. }
      rewrite N.shiftl_mul_pow2.
      apply (N.lt_le_trans _ (2^32 * 2^32)).
      2:{ cbn; lia. }
      apply N.mul_lt_mono_pos_r.
      { lia. }
      rewrite N.land_ones.
      apply N.mod_upper_bound.
      lia.
    }

    {
      rewrite Hbuff_len.
      autorewrite with tuple_if;
      cbn [fst snd negb].
      destr (input_valid);
      destr (flush);
      destr (4 <=? length state_data)%nat;
      destr (4 <=? N.of_nat (length state_data))%N;
      boolsimpl; try lia.

      { rewrite N.add_sub_swap by lia.
        cbn [N.of_nat].
        replace (2 ^ 4)%N with (1 * 2 ^ 4)%N at 1 by lia.
        rewrite N.mod_add by now cbn.
        rewrite N.mod_small; cbn; lia.
      }
      { rewrite N.add_sub_swap by lia.
        replace (2 ^ 4)%N with (1 * 2 ^ 4)%N at 1 by lia.
        rewrite N.mod_add by now cbn.
        rewrite N.mod_small by ( cbn; subst; lia ).
        rewrite N.shiftr_0_r.
        cbv [realign_inner_spec ]; subst; stepsimpl;
        autorewrite with tuple_if;
        cbn [fst snd]; rewrite unfold_N_to_bytes_4.
        push_length.
        replace input_mask with (N.of_nat (N.to_nat input_mask)) by apply N2Nat.id.
        remember (N.to_nat input_mask) as x.
        do 14 (destruct x; [cbn; lia|]).
        repeat match goal with
        | |- context [?X =? ?Y] => destr (X =? Y); try lia
        end.
      }
      {
        cbv [realign_inner_spec ]; subst; stepsimpl;
        autorewrite with tuple_if;
        cbn [fst snd]; rewrite unfold_N_to_bytes_4.
        push_length.
        replace input_mask with (N.of_nat (N.to_nat input_mask)) by apply N2Nat.id.
        remember (N.to_nat input_mask) as x.
        do 14 (destruct x; [cbn; lia|]).
        repeat match goal with
        | |- context [?X =? ?Y] => destr (X =? Y); try lia
        end.
      }
      { rewrite N.add_sub_swap by lia.
        replace (2 ^ 4)%N with (1 * 2 ^ 4)%N at 1 by lia.
        rewrite N.mod_add by now cbn.
        rewrite N.mod_small; cbn; lia.
      }
      { rewrite N.add_sub_swap by lia.
        cbn [N.of_nat].
        replace (2 ^ 4)%N with (1 * 2 ^ 4)%N at 1 by lia.
        rewrite N.mod_add by now cbn.
        rewrite N.mod_small; cbn; lia.
      }
    }
  Qed.

  Lemma step_realign
    latched_valid
    latched_bytes
      state_data
      (input : denote_type (input_of (realign (var:=denote_type) )))
      (state : denote_type (state_of (realign (var:=denote_type) ))) :
    realign_pre input state ->
    realign_invariant latched_valid latched_bytes state_data state ->
    snd (step realign state input) = realign_spec latched_valid latched_bytes state_data input.
  Proof.
    destruct input as (input_valid, (input_data, (input_mask, (flush, (consumer_ready, []))))).
    destruct state as (out_valid, (out_data, (out_length, (q, q_len)))).
    intros Hpre Hinv.

    destruct Hinv as [Hbuff_len [Hlatch_valid [Hlatch_bytes [Hlatch_bytes_len [Hfirst_bytes Hbuf_bound]]]]].
    subst.

    cbv [realign realign_spec realign_pre realign_invariant realign_update_state K] in *.
    stepsimpl.

    repeat (destruct_pair_let; cbn[fst snd]).
    autorewrite with tuple_if.
    erewrite step_realign_inner.
    {
      cbn [fst snd].
      rewrite <- Hlatch_bytes_len.
      rewrite N2Nat.id.
      cbv [bvslice bvresize bvmin].
      stepsimpl.
      rewrite resize_firstn by lia.
      rewrite N.land_ones.
      rewrite N.land_ones.
      rewrite concat_bytes_truncation.

      replace
        ((if N.of_nat (length state_data) <=? 4
          then N.of_nat (length state_data)
          else 4) mod 2 ^ N.of_nat 4)%N with
          (N.of_nat (length (firstn 4 state_data))).
      2:{
        destr (length state_data <=? 4)%nat;
        destr (N.of_nat (length state_data) <=? 4); try lia.
        { rewrite firstn_length.
          rewrite Nat.min_r by lia.
          now rewrite N.mod_small by (cbn;lia).
        }
        { rewrite firstn_length.
          rewrite Nat.min_l by lia.
          now rewrite N.mod_small by (cbn;lia).
        }
      }

      destr (1 <=? length state_data)%nat;
      destr (1 <=? N.of_nat (length state_data));
      destr (4 <=? length state_data)%nat;
      destr (4 <=? N.of_nat (length state_data)); try lia;
      reflexivity.
    }
    cbn [realign_inner_pre].
    ssplit.
    {
      cbv [bvslice bvresize bvmin].
      stepsimpl.
      repeat rewrite N.land_ones.
      destruct ((4 <=? N.of_nat (length state_data)) || flush)%N;
      apply N.mod_upper_bound; lia.
    }
    {
      cbv [bvslice bvresize bvmin].
      stepsimpl.
      destr (4 <=? length state_data)%nat;
      destr (4 <=? N.of_nat (length state_data))%N;
      try lia.
      {
        rewrite N.add_sub_swap by lia.
        replace 16%N with (1*16)%N at 1 by lia. rewrite N.mod_add by now cbn.
        rewrite N.mod_small by (cbn; lia).
        destruct flush; cbn; lia.
      }
      destruct flush; cbn; lia.
    }
    { easy. }
    { reflexivity. }
  Qed.

End RealignerSpec.
