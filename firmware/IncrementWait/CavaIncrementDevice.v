Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Invariant.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.TLUL.
Require Import Cava.Types.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.

Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface coqutil.Word.Properties.

Require Import riscv.Utility.Utility.

Require Import bedrock2.ZnWords.

Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.Incr.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Import ListNotations.

Section WithParameters.
  Instance var : tvar := denote_type.

  Existing Instance Incr.inner_specification.
  Existing Instance Incr.inner_correctness.
  Existing Instance Incr.inner_invariant.

  Existing Instance TLUL.tl_specification.
  Existing Instance TLUL.tlul_invariant.
  Existing Instance TLUL.tlul_adapter_reg_correctness.

  Existing Instance incr_specification.
  Existing Instance incr_invariant.
  Existing Instance incr_correctness.

  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Global Instance counter_device: device := {|
    device.state := denote_type (state_of incr);
    device.is_ready_state s := exists r_prev_state r_regs r_inner,
        incr_invariant s (RSIdle, r_prev_state, r_regs, TLUL.Idle, r_inner);
    device.last_d2h '((_, (_, (_, d2h))), _) := d2h;
    device.tl_inflight_ops '((_, (_, (_, d2h))), _) :=
      if d_valid d2h then [d_source d2h] else [];
    device.run1 s i := fst (Semantics.step incr s (i, tt));
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay '((_, (_, (_, d2h))), _) :=
      if a_ready d2h then 2
      else if d_valid d2h then 1
           else 0;
    (* The last [else] is not reachable, because [d_valid] is always the
       negation of [a_ready]. *)
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.


  Inductive counter_related_base: IncrementWaitSemantics.state -> Incr.repr_state -> Incr.inner_state -> Prop :=
  | IDLE_related: forall r_innr,
      counter_related_base IDLE RSIdle r_innr
  | BUSY1_related: forall val ncycles,
      (1 < ncycles)%nat ->
      counter_related_base (BUSY val ncycles) (RSBusy (word_to_N val))
                           (IISBusy (word_to_N val) 1)
  | BUSY2_related: forall val ncycles,
      (0 < ncycles)%nat ->
      counter_related_base (BUSY val ncycles) (RSBusy (word_to_N val))
                           (IISBusy (word_to_N val) 2)
  (* the hardware is already done, but the software hasn't polled it yet to find out,
     so we have to relate a software-BUSY to a hardware-done: *)
  | BUSY_done_related: forall val ncycles r_innr,
      counter_related_base (BUSY val ncycles) (RSDone (word_to_N (word.add (word.of_Z 1) val))) r_innr
  | DONE_related: forall val r_innr,
      counter_related_base (DONE val) (RSDone (word_to_N val)) r_innr.

  Inductive counter_related_spec: IncrementWaitSemantics.state -> repr ->
                                  list tl_h2d -> Prop :=
  | No_inflight: forall sH r_state r_prev_state r_regs r_inner,
      counter_related_base sH r_state r_inner ->
      counter_related_spec sH (r_state, r_prev_state, r_regs, TLUL.Idle, r_inner) []
  | Inflight_read_status: forall sH r_state r_prev_state r_regs r_tl r_tl_regs r_inner h2d,
      counter_related_base sH r_state r_inner ->
      r_tl = TLUL.OutstandingAccessAckData (set_a_address 4 h2d) r_tl_regs ->
      a_valid h2d = true ->
      a_opcode h2d = Get ->
      a_address h2d = word_to_N (state_machine.reg_addr STATUS) ->
      counter_related_spec sH (r_state, r_prev_state, r_regs, r_tl, r_inner) [h2d]
  | Inflight_read_value: forall r_prev_state r_regs r_tl r_tl_regs r_inner val h2d,
      r_tl = TLUL.OutstandingAccessAckData (set_a_address 0 h2d) r_tl_regs ->
      nth 0 r_tl_regs 0%N = word_to_N val ->
      a_valid h2d = true ->
      a_opcode h2d = Get ->
      a_address h2d = word_to_N (state_machine.reg_addr VALUE) ->
      counter_related_spec (DONE val)
                           (RSIdle, r_prev_state, r_regs, r_tl, r_inner)
                           [h2d]
  | Inflight_write_value: forall r_prev_state r_regs r_tl r_inner val h2d,
      r_tl = TLUL.OutstandingAccessAck (set_a_address 0 h2d) ->
      a_valid h2d = true ->
      a_opcode h2d = PutFullData ->
      a_address h2d = word_to_N (state_machine.reg_addr VALUE) ->
      a_data h2d = (word_to_N val) ->
      counter_related_spec (IDLE)
                           (RSBusy (word_to_N val), r_prev_state, r_regs, r_tl, r_inner)
                           [h2d].

  Definition counter_related {invariant : invariant_for incr repr} (sH : IncrementWaitSemantics.state)
             (sL : denote_type (state_of incr)) (inflight_h2ds : list tl_h2d) : Prop :=
    exists repr, counter_related_spec sH repr inflight_h2ds /\ invariant sL repr.

  (* This should be in bedrock2.ZnWords. It is use by ZnWords, which is used in
     the two following Lemmas. *)
  Ltac better_lia ::= Zify.zify; Z.to_euclidean_division_equations; lia.

  Lemma incrN_word_to_bv: forall (x : word),
      ((N.add (word_to_N x) 1) mod 4294967296)%N = word_to_N (word.add (word.of_Z 1) x).
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Lemma Z_word_N: forall (x : Z),
      (0 <= x < 2 ^ 32)%Z -> word_to_N (word.of_Z x) = Z.to_N x.
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Set Printing Depth 100000.

  Ltac destruct_pair_let_hyp :=
    match goal with
    | H: context [ match ?p with
                   | pair _ _ => _
                   end ] |- _ =>
      destruct p as [?p0 ?p1] eqn:?H0
    end.

  Ltac destruct_pair_equal_hyp :=
    match goal with
    | H: context [ (?l0, ?l1) = (?r0, ?r1) ] |- _ =>
      eapply pair_equal_spec in H; destruct H as [?H0 ?H1]
    end.

  Lemma N_to_word_word_to_N: forall v, N_to_word (word_to_N v) = v.
  Proof. intros. unfold N_to_word, word_to_N. ZnWords. Qed.

(* TODO move to coqutil *)
Ltac contradictory H :=
  lazymatch type of H with
  | ?x <> ?x => exfalso; apply (H eq_refl)
  | False => case H
  end.

Require Import coqutil.Tactics.autoforward.

Ltac fwd_step ::=
  match goal with
  | H: ?T |- _ => is_destructible_and T; destr_and H
  | H: exists y, _ |- _ => let yf := fresh y in destruct H as [yf H]
  | H: ?x = ?x |- _ => clear H
  | H: True |- _ => clear H
  | H: ?LHS = ?RHS |- _ =>
    let h1 := head_of_app LHS in is_constructor h1;
    let h2 := head_of_app RHS in is_constructor h2;
    (* if not eq, H is a contradiction, but we don't want to change the number
       of open goals in this tactic *)
    constr_eq h1 h2;
    (* we don't use `inversion H` or `injection H` because they unfold definitions *)
    inv_rec LHS RHS;
    clear H
  | E: ?x = ?RHS |- context[match ?x with _ => _ end] =>
    let h := head_of_app RHS in is_constructor h; rewrite E in *
  | H: context[match ?x with _ => _ end], E: ?x = ?RHS |- _ =>
    let h := head_of_app RHS in is_constructor h; rewrite E in *
  | H: context[match ?x with _ => _ end] |- _ =>
    (* note: recursive invocation of fwd_step for contradictory cases *)
    destr x; try solve [repeat fwd_step; contradictory H]; []
  | H: _ |- _ => autoforward with typeclass_instances in H
  | |- _ => progress subst
  | |- _ => progress fwd_rewrites
  end.

  Axiom TODO: False.

  Ltac use_spec :=
    match goal with
    | Hrun: device.run1 ?sL ?input = ?sL',
            Hinv: incr_invariant ?sL ?repr
      |- _ =>
      assert (Hprec: precondition incr (input, tt) repr);
      [|
       (* pose proof (output_correct_pf (c:=incr) (input, tt) sL repr Hinv Hprec) as Hpostc. *)
       remember (update_repr (c:=incr) (input, tt) repr) as repr' eqn:Erepr';
       pose proof (invariant_preserved_pf (c:=incr) (input, tt) sL repr repr' Erepr' Hinv Hprec) as Hinv';
       unfold device.run1, counter_device in Hrun;
       match type of Hrun with
       | fst ?step = _ =>
         remember step as res eqn:Hstep;
         destruct res as (?sL'' & ?d2h);
         cbn in Hrun; subst sL''; clear Hstep
       end;
       cbn [fst] in Hinv']
    end.

  Ltac inversion_rel_spec :=
    match goal with
    | H: counter_related_spec _ _ _ |- _ => inversion H; subst
    end.
  Ltac inversion_rel_base :=
    match goal with
    | H: counter_related_base _ _ _ |- _ => inversion H; subst
    end.

  (* Lemma output_last_d2h : forall s h2d s' d2h, *)
  (*     (s', d2h) = Semantics.step incr s (h2d, tt) -> *)
  (*     device.last_d2h s' = d2h. *)
  (* Proof. *)

  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device increment_wait_state_machine.
  Proof.
    eapply Build_device_implements_state_machine with (device_state_related := counter_related).
    - (* mmioAddrs_match: *)
      reflexivity.
    - (* initial_state_is_ready_state: *)
      intros ? ? ? Hrel.
      cbn in *. subst. destruct Hrel as [?repr [?Hrel ?Hinv]].
      inversion_rel_spec. inversion_rel_base.
      repeat eexists. eapply Hinv.
    - (* initial_states_are_related: *)
      intros ? ? ? Hready.
      cbn in *. destruct Hready as (?r_prev_state & ?r_regs & ?r_inner & ?Hinv). subst.
      unfold counter_related. eexists. split; [|apply Hinv].
      apply No_inflight, IDLE_related.
    - (* initial_state_exists: *)
      intros ? Hready.
      cbn in *. destruct Hready as (?r_prev_state & ?r_regs & ?r_inner & ?Hinv).
      eexists. split; [reflexivity|].
      unfold counter_related. eexists. split; [|apply Hinv].
      apply No_inflight, IDLE_related.
    - (* nonMMIO_device_step_preserves_state_machine_state: *)
      intros ? ? ? ? Ha_valid [repr [Hrel Hinv]] **.
      use_spec.
      { destruct_tl_h2d. destruct_tl_d2h. tlsimpl.
        cbn in sL1; destruct sL1 as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
        destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner).
        simplify_invariant incr. logical_simplify.
        subst. cbn. ssplit; intros; [auto|discriminate|auto].
      }
      exists repr'; split; [|auto].
      inversion_rel_spec; inversion_rel_base;
        destruct_tl_h2d; destruct_tl_d2h; tlsimpl; subst;
          cbn in sL1; destruct sL1 as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
            simplify_invariant incr; logical_simplify; subst; cbn -[replace];
              apply No_inflight; try (constructor; lia); [].
      replace ((word_to_N val + 1) mod 4294967296)%N with
          (word_to_N (word.add (word.of_Z 1) val)) by
          (unfold word_to_N; ZnWords);
        apply BUSY_done_related.

    - (* [state_machine_read_to_device_send_read_or_later] *)
      intros ? ? ? ? ? ? [v [sH'' Hex_read]] [repr [Hrel Hinv]] **.
      cbn in Hex_read. logical_simplify.
      rewrite H5. clear H5.
      use_spec.
      1: simplify_spec incr; simplify_spec (tlul_adapter_reg (reg_count:=2)); simplify_spec Incr.inner;
        simplify_invariant incr;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner);
          destruct_tl_h2d; tlsimpl; logical_simplify; subst;
            ssplit; intros; auto.

      destruct_one_match; [destruct_one_match|].
      (* case 1: device ready, valid response
           In our TL implementation [a_ready = negb d_valid], hence this case
           is not possible.
           case 3: device not ready
           If the inflight queue is empty, the device must be ready, hence
           this case is not possible. *)
      1,3: exfalso;
        unfold device.last_d2h, counter_device in *;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner);
          simplify_invariant incr; subst; logical_simplify; destruct_tl_d2h; tlsimpl; subst;
          inversion_rel_spec; logical_simplify; discriminate.
      (* device ready, no valid response: *)
      ssplit.
      1: eexists; split; [|eassumption]; [].
      all:
        unfold device.tl_inflight_ops, device.last_d2h, device.maxRespDelay,
        counter_device, counter_related in *;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          cbn in sL'; destruct sL' as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
            destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner);
            destruct_tl_d2h; destruct_tl_h2d;
              simplify_spec incr; simplify_spec (tlul_adapter_reg (reg_count:=2));
                simplify_invariant incr;
                logical_simplify; tlsimpl; subst;
                  cbn in Hinv'; logical_simplify; subst.
      + destruct r.
        * (* [r:=VALUE] *)
          inversion_rel_spec; inversion_rel_base; destruct H6; subst.
          cbn; replace (N.land (word_to_N (word.of_Z 16384)) 4) with 0%N
            by (rewrite Z_word_N by lia; reflexivity);
          cbn; eapply Inflight_read_value; [eauto| |reflexivity..].
          logical_simplify. assumption.
        * (* [r:=STATUS] *)
          inversion_rel_spec; inversion_rel_base; subst; logical_simplify; subst; cbn.
            eapply Inflight_read_status; try (constructor; lia).
          all: replace (N.land (word_to_N (word.of_Z 16388)) 4) with 4%N
            by (rewrite Z_word_N by lia; reflexivity); eauto.
          all: cbn; replace ((word_to_N val + 1) mod 4294967296)%N with
                        (word_to_N (word.add (word.of_Z 1) val)) by
              (unfold word_to_N; ZnWords); constructor.

      + inversion_rel_spec; inversion_rel_base; subst; logical_simplify; subst; lia.

    - (* [state_machine_read_to_device_ack_read_or_later] *)
      intros ? ? ? ? ? ? [v [sH'' Hex_read]] [repr [Hrel Hinv]] **.
      (* assert (Hex_rel: exists sL'' h2d', device.run1 sL'' (set_d_ready true h2d') = sL /\ *)
      (*                               counter_related sH sL'' []). *)
      (* { admit. } *)
      (* logical_simplify. destruct H0 as [repr'' [Hrel'' Hinv'']]. *)
      (* use_spec. 1: admit. *)
      (* rename Hprec into Hprec''. rename repr' into repr'''. rename Erepr' into Erepr''. rename Hinv' into Hinv'''. *)
      cbn in Hex_read. logical_simplify.
      rewrite H2. clear H2. rename H3 into Hex_read.
      use_spec.
      1: simplify_spec incr; simplify_spec (tlul_adapter_reg (reg_count:=2)); simplify_spec Incr.inner;
        simplify_invariant incr;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          destruct repr as (((?r_state, ?r_regs), ?r_tl), ?r_inner);
          destruct r_state;
          destruct_tl_h2d; tlsimpl; logical_simplify; subst;
            ssplit; intros; auto.

      destruct_one_match.
      (* case 2: no valid response
         If the inflight queue is not empty, the device must be sending a
         response, hence this case is not possible. *)
      2: unfold device.last_d2h, counter_device in *;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          destruct repr as (((?r_state, ?r_regs), ?r_tl), ?r_inner);
          simplify_invariant incr; subst; logical_simplify; destruct_tl_d2h; tlsimpl; subst;
            inversion_rel_spec; try inversion_rel_base; logical_simplify; subst;
              try destruct r_tl; logical_simplify; subst;
                discriminate.

      (* case 1: valid response *)
      destruct r.
      + (* [r:=VALUE] *)
        inversion_rel_spec;
          try (exfalso; destruct_tl_h2d; tlsimpl; subst; unfold word_to_N in *; cbn in *; ZnWords).

        destruct Hex_read; subst.
        logical_simplify; subst.
        exists IDLE. ssplit.
        * eexists. split; [|eassumption].
          cbn.
          cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
            simplify_invariant incr;
            logical_simplify; tlsimpl; subst.
          apply No_inflight, IDLE_related.
        * cbn. ssplit; try reflexivity.
          clear Hinv'.
          cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          simplify_invariant incr.
          logical_simplify; subst.
          destruct_tl_h2d; tlsimpl; subst.
          rewrite H19. cbn. rewrite H3. apply N_to_word_word_to_N.
      + (* [r:=STATUS] *)
        inversion_rel_spec;
          try (exfalso; destruct_tl_h2d; tlsimpl; subst; unfold word_to_N in *; cbn in *; ZnWords).

        inversion_rel_base;
          cbn in sL |- *; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
            simplify_invariant incr;
            logical_simplify; subst; logical_simplify; subst;
              match goal with
              | H: d_data _ = _ |- _ =>
                rewrite H
              end;
              cbn; destruct_tl_h2d; tlsimpl; subst; cbn;
              change (Pos.to_nat 1) with 1.
                (* match goal with *)
                (* | H: nth 1 r_tl_regs 0%N = _ |- _ => rewrite H *)
                (* end; *)
                (* unfold N_to_word, status_value. *)
        * eexists; ssplit; try reflexivity.
          -- eexists.
             ssplit; [|eassumption].
             apply No_inflight. constructor.
          -- assert (Hprev: r_prev_state = RSIdle) by admit.
             subst.
             match goal with
             | H: nth 1 r_tl_regs 0%N = _ |- _ => rewrite H
             end; unfold N_to_word, status_value.
             ZnWords.
        * destruct ncycles as [|ncycles]; [lia|].
          eexists; ssplit; try reflexivity.
          -- eexists. ssplit; [|eassumption].
             apply No_inflight, BUSY2_related. apply lt_S_n. eauto.
          -- right. eexists. ssplit; [reflexivity| |reflexivity].
             assert (Hprev: exists d, r_prev_state = RSBusy d) by admit.
             logical_simplify; subst.
             match goal with
             | H: nth 1 r_tl_regs 0%N = _ |- _ => rewrite H
             end; unfold N_to_word, status_value.
             ZnWords.
        * destruct ncycles as [|ncycles]; [lia|].
          eexists. ssplit; try reflexivity.
          -- eexists. ssplit; [|eassumption].
             cbn; rewrite incrN_word_to_bv.
             apply No_inflight, BUSY_done_related.
          -- right. eexists. ssplit; [reflexivity| |reflexivity].
             assert (Hprev: exists d, r_prev_state = RSBusy d) by admit.
             logical_simplify; subst.
             match goal with
             | H: nth 1 r_tl_regs 0%N = _ |- _ => rewrite H
             end; unfold N_to_word, status_value.
             ZnWords.
        * eexists; ssplit; try reflexivity.
          -- eexists. ssplit; [|eassumption].
             apply No_inflight, DONE_related.
          -- left. ssplit; [|reflexivity].
             assert (Hprev: exists d, r_prev_state = RSDone d) by admit.
             logical_simplify; subst; logical_simplify;
             match goal with
             | H: nth 1 r_tl_regs 0%N = _ |- _ => rewrite H
             end; unfold N_to_word, status_value.
             ZnWords.
        * eexists; ssplit; try reflexivity.
          -- eexists. ssplit; [|eassumption].
             apply No_inflight, DONE_related.
          -- assert (Hprev: exists d, r_prev_state = RSDone d) by admit.
             logical_simplify; subst; logical_simplify.
             match goal with
             | H: nth 1 r_tl_regs 0%N = _ |- _ => rewrite H
             end; unfold N_to_word, status_value.
             ZnWords.

    - (* [state_machine_write_to_device_send_write_or_later] *)
      intros ? ? ? ? ? ? ? [sH'' [Hpow2 Hex_write]] [repr [Hrel Hinv]] **.
      rewrite Hpow2. clear Hpow2.
      use_spec.
      1: simplify_spec incr; simplify_spec (tlul_adapter_reg (reg_count:=2)); simplify_spec Incr.inner;
        simplify_invariant incr;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner);
          destruct_tl_h2d; tlsimpl; logical_simplify; subst;
            ssplit; intros; auto.

      destruct_one_match; [destruct_one_match|].
        (* case 1: device ready, valid response
           In our TL implementation [a_ready = negb d_valid], hence this case
           is not possible.
           case 3: device not ready
           If the inflight queue is empty, the device must be ready, hence
           this case is not possible. *)
      1,3: exfalso;
        unfold device.last_d2h, counter_device in *;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
        destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner);
          simplify_invariant incr; subst; logical_simplify; destruct_tl_d2h; tlsimpl; subst;
            inversion_rel_spec; logical_simplify; discriminate.
      (* device ready, no valid response: *)
      ssplit.
      1: eexists; split; [|eassumption]; [].
      all:
        unfold device.tl_inflight_ops, device.last_d2h, device.maxRespDelay,
        counter_device, counter_related in *;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          cbn in sL'; destruct sL' as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
            destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner);
            destruct_tl_d2h; destruct_tl_h2d;
              simplify_spec incr; simplify_spec (tlul_adapter_reg (reg_count:=2));
                simplify_invariant incr;
                logical_simplify; tlsimpl; subst;
                  cbn in Hinv'; logical_simplify; subst.
      + destruct r.
        * (* [r:=VALUE] *)
          inversion_rel_spec; inversion_rel_base; logical_simplify; subst; try contradiction.
          cbn. apply Inflight_write_value; eauto; [].
          rewrite Z_word_N by lia. change (Z.to_N 16384) with 16384%N. reflexivity.
        * (* [r:=STATUS] *)
          inversion_rel_spec; inversion_rel_base;
          destruct Hex_write.
      + inversion_rel_spec; inversion_rel_base; subst; logical_simplify; subst; lia.

    - (* [state_machine_write_to_device_ack_write_or_later] *)
      intros ? ? ? ? ? ? ? [sH'' [Hpow2 Hex_write]] [repr [Hrel Hinv]] **.
      rewrite Hpow2 in *. clear Hpow2.
      use_spec.
      1: simplify_spec incr; simplify_spec (tlul_adapter_reg (reg_count:=2)); simplify_spec Incr.inner;
        simplify_invariant incr;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner);
          destruct_tl_h2d; tlsimpl; logical_simplify; subst;
            ssplit; intros; auto.

      destruct_one_match.
      (* case 2: no valid response
         If the inflight queue is not empty, the device must be sending a
         response, hence this case is not possible. *)
      2: unfold device.last_d2h, counter_device in *;
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
          destruct repr as ((((?r_state, ?r_prev_state), ?r_regs), ?r_tl), ?r_inner);
          simplify_invariant incr; subst; logical_simplify; destruct_tl_d2h; tlsimpl; subst;
            inversion_rel_spec; try inversion_rel_base; logical_simplify; subst;
              try destruct r_tl; logical_simplify; subst;
                discriminate.

      (* case 1: valid response *)
      destruct r.
      + (* [r:=VALUE] *)
        inversion_rel_spec;
          try (exfalso; destruct_tl_h2d; tlsimpl; subst; unfold word_to_N in *; cbn in *; ZnWords).

        destruct Hex_write; subst.
        logical_simplify; subst.
        eexists. ssplit; [|cbn; split; reflexivity].
        eexists. split; [|eassumption].
        cbn.
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
            simplify_invariant incr;
            logical_simplify; tlsimpl; subst.
        apply No_inflight.
        simplify_invariant Incr.inner; destruct s_inner; logical_simplify.
        destruct x as [|[|[|]]]; [exfalso; lia|..| exfalso; lia];
          destruct_tl_h2d; tlsimpl; subst;
            match goal with
            | H: word_to_N v = word_to_N val |- _ =>
              rewrite <- H
            end.
        * constructor; lia.
        * replace ((word_to_N v + 1) mod 4294967296)%N with
                        (word_to_N (word.add (word.of_Z 1) v)) by
              (unfold word_to_N; ZnWords).
          constructor.
      + (* [r:=STATUS] *)
        inversion_rel_spec;
          try (exfalso; destruct_tl_h2d; tlsimpl; subst; unfold word_to_N in *; cbn in *; ZnWords).
    - (* read_step_unique: *)
      intros. simpl in *. unfold read_step in *. simp.
      destruct v; destruct r; try contradiction; simp; try reflexivity.
      destruct Hp1; destruct H0p1; simp; try reflexivity;
        unfold status_value in *; exfalso; ZnWords.
    - (* write_step_unique: *)
      intros. simpl in *. unfold write_step in *. simp. subst. reflexivity.
    - (* initial_state_unique: *)
      intros. simpl in *. subst. reflexivity.
  Qed.
End WithParameters.
