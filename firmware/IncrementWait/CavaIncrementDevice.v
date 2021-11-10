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

  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Global Instance counter_device: device := {|
    device.state := denote_type (state_of incr);
    device.is_ready_state s := exists r_regs r_tlul r_inner,
        incr_invariant s (RSIdle, r_regs, r_tlul, r_inner);
    device.run1 s i := Semantics.step incr s (i, tt);
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay '((istate, (val, tl_d2h)), tlul_state) h2d :=
      (* if the value register was requested, and we're in state Busy1, it will take one
         more cycle to respond, else we will respond immediately *)
      if ((a_address h2d mod 8 =? 0(*register address=VALUE*))%N && (istate =? 1 (*Busy1*))%N)%bool
      then 1%nat else 0%nat;
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.

  Inductive counter_related_spec: IncrementWaitSemantics.state -> repr -> Prop :=
  | IDLE_related: forall r_regs r_tl r_inner,
      counter_related_spec IDLE (RSIdle, r_regs, r_tl, r_inner)
  | BUSY_related: forall r_regs r_tl r_inner val ncycles,
      (0 < ncycles)%nat ->
      counter_related_spec (BUSY val ncycles)
                           (RSBusy (word_to_N val), r_regs, r_tl, r_inner)
  (* the hardware is already done, but the software hasn't polled it yet to find out,
     so we have to relate a software-BUSY to a hardware-done: *)
  | BUSY_done_related: forall r_regs r_tl r_inner val ncycles,
      counter_related_spec (BUSY val ncycles)
                           (RSDone (word_to_N (word.add (word.of_Z 1) val)), r_regs, r_tl, r_inner)
  | DONE_related: forall r_regs r_tl r_inner val,
      nth 0 r_regs 0%N = (word_to_N val)
      -> counter_related_spec (DONE val)
                             (RSDone (word_to_N val), r_regs, r_tl, r_inner).

  Definition counter_related (sH : IncrementWaitSemantics.state)
             (sL : denote_type (state_of incr)) : Prop :=
    exists repr, counter_related_spec sH repr /\ incr_invariant sL repr.

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

  (* Ltac destruct_tlul_adapter_reg_state := *)
  (*   match goal with *)
  (*   | H : N * (N * (N * (bool * (bool * (bool * bool))))) |- _ => *)
  (*     destruct H as [?reqid [?reqsz [?rspop [?error [?outstanding [?we_o ?re_o]]]]]] *)
  (*   end. *)

  Lemma N_to_word_word_to_N: forall v, N_to_word (word_to_N v) = v.
  Proof. intros. unfold N_to_word, word_to_N. ZnWords. Qed.

  Existing Instance Incr.inner_specification.
  Existing Instance Incr.inner_correctness.
  Existing Instance Incr.inner_invariant.

  Existing Instance TLUL.tlul_specification.
  Existing Instance TLUL.tlul_adapter_reg_correctness.
  Existing Instance TLUL.tlul_invariant.

  Existing Instance incr_specification.
  Existing Instance incr_correctness.

  Lemma runUntilResp_big_step : forall s h2d repr,
      precondition incr (h2d, tt) repr
      -> a_valid h2d = true
      -> d_ready h2d = true (* TODO: do we need this? *)
      -> incr_invariant s repr
      -> exists n inputs s' repr' d2h s'',
          device.runUntilResp h2d device.maxRespDelay s = (Some d2h, s'')
          /\ n <= device.maxRespDelay
          /\ inputs = repeat (h2d, tt) n
          /\ s' = snd (simulate' incr inputs s)
          (* /\ (s'', d2h) = Semantics.step incr s' (h2d, tt) *)
          /\ repr' = fold_left (fun r i => update_repr (c:=incr) i r) inputs repr
          (* /\ invariant s' repr' *)
          /\ postcondition incr (h2d, tt) repr' d2h
          /\ d_valid d2h = true
          /\ incr_invariant s'' (update_repr (c:=incr) (h2d, tt) repr').
  Proof.
    intros ? ? ? Hprec Ea_valid Ed_ready Hinv.
    unfold device.maxRespDelay, device.runUntilResp, device.state, device.run1, counter_device,
    state_machine.read_step, increment_wait_state_machine, read_step in *.
    eapply output_correct_pf in Hinv as Houtput.
    apply Houtput in Hprec as Hpostc. clear Houtput.
    cbn in s, h2d. destruct_tl_h2d.
    destruct repr as (((?r_state, ?r_regs), ?r_tl), ?r_inner).
    assert (Hprec_temp := Hprec).
    unfold precondition, incr_specification in Hprec_temp.
    logical_simplify.
    unfold precondition, tlul_specification in H.
    logical_simplify. tlsimpl. subst.
    unfold postcondition, incr_specification in Hpostc.
    unfold postcondition, tlul_specification in Hpostc.
    destruct Hpostc as [[is_read [is_write [address [w_val w_mask]]]] [h2d' [regs' [d2h' [is_read' [is_write' [address' [w_val' [w_mask' Hpostc]]]]]]]]].
    destruct_tl_h2d. destruct_tl_d2h. tlsimpl.
    destruct Hpostc as [Hpostc1 [Hpostc2 Hpostc3]].
    subst.
    apply pair_equal_spec in Hpostc2.
    logical_simplify.
    cbn [outstanding_h2d] in Hpostc3.
    destruct (outstanding_h2d r_tl) eqn:Eouts.
    - cbn in Hpostc3. logical_simplify. subst.
      assert (Hprec':
                precondition incr
                             (true,
                              (a_opcode0,
                               (a_param0, (a_size0, (a_source0, (a_address, (a_mask0, (a_data0, (a_user0, true)))))))), tt)
                             (update_repr (c:=incr)
                                          (true,
                                           (a_opcode0,
                                            (a_param0, (a_size0, (a_source0, (a_address, (a_mask0, (a_data0, (a_user0, true)))))))), tt)
                                          (r_state, regs', r_tl, r_inner))).
      { simplify_spec incr.
        cbn [outstanding_h2d]. rewrite Eouts.
        tlsimpl. ssplit.
        - simplify_spec (tlul_adapter_reg (reg_count:=2)). tlsimpl. split; [|assumption].
          match goal with
          | |- context [length (match ?m with | _=> _ end)] =>
            destruct m
          end;
          match goal with
          | |- context [replace _ _ (match ?m with | _=> _ end)] =>
            destruct m
          end; rewrite ! length_replace; assumption.
        - simplify_spec Incr.inner. intros. apply I.
      }
      destruct H1; [auto|..]; subst.
      all: exists 1.
      all: destruct_pair_let;
        match goal with
        | |- context [if d_valid ?c then _ else _] =>
          match type of H2 with
          | _ = ?r => replace c with r
          end
        end.
      all: tlsimpl;
        assert (Hinv' := Hprec);
        eapply incr_invariant_preserved in Hinv;
        [apply Hinv in Hinv'|reflexivity]; clear Hinv.
      all: eapply output_correct_pf in Hinv' as Houtput';
        apply Houtput' in Hprec' as Hpostc'; clear Houtput';
          assert (Hpostc'' := Hpostc');
        unfold postcondition, incr_specification in Hpostc';
        unfold postcondition, tlul_specification in Hpostc';
        cbn [update_repr outstanding_h2d] in Hpostc';
        rewrite Eouts in Hpostc'; cbn -[Semantics.step] in Hpostc';
        destruct Hpostc' as [[is_read [is_write [address [w_val w_mask]]]] [h2d' [regs'' [d2h' [is_read' [is_write' [address'' [w_val'' [w_mask'' Hpostc']]]]]]]]].
      all: destruct_tl_h2d; destruct_tl_d2h; tlsimpl;
        destruct Hpostc' as [Hpostc1' [Hpostc2' Hpostc3']];
        subst;
        apply pair_equal_spec in Hpostc2';
        logical_simplify;
        rewrite Eouts in Hpostc3';
        tlsimpl.
      all: cbn in Hpostc3'; logical_simplify; subst.
      all: do 5 eexists; ssplit; try reflexivity.
      1,5: destruct_pair_let;
                match goal with
        | |- context [if d_valid ?c then _ else _] =>
          match type of H1 with
          | _ = ?r => replace c with r
          end
        end; tlsimpl; reflexivity.
      1,4: cbn [repeat fold_left];
        match goal with
        | H: postcondition incr _ _ ?c |- _ =>
          match type of H1 with
          | _ = ?r => replace c with r in H; apply H
          end
        end.
      1,3: reflexivity.
      1,2: cbn [repeat fold_left];
        eapply incr_invariant_preserved; [reflexivity|assumption..].
    - destruct H1; [auto|..]; subst; cbn in Hpostc3; logical_simplify; subst.
      all: exists 0.
      all: do 5 eexists; ssplit; try reflexivity; try lia.
      1,5: destruct_pair_let;
        match goal with
        | |- context [if d_valid ?c then _ else _] =>
          match type of H2 with
          | _ = ?r => replace c with r
          end
        end; tlsimpl; reflexivity.
      1,4: cbn [repeat fold_left];
        eapply output_correct_pf in Hinv as Houtput;
        apply Houtput in Hprec;
        match goal with
        | H: postcondition incr _ _ ?c |- _ =>
          match type of H2 with
          | _ = ?r => replace c with r in H; apply H
          end
        end.
      1,3: reflexivity.
      1,2: cbn [repeat fold_left];
        eapply incr_invariant_preserved; [reflexivity|assumption..].
  Qed.

  (* Set Printing All. *)
  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device increment_wait_state_machine.
  Proof.
    eapply Build_device_implements_state_machine with (device_state_related := counter_related).
    - (* mmioAddrs_match: *)
      reflexivity.
    - (* initial_state_is_ready_state: *)
      intros ? ? Hinit Hrel.
      cbn in *. subst. destruct Hrel as [?repr [?Hrel ?Hinv]].
      inversion Hrel. subst.
      do 3 eexists. eapply Hinv.
    - (* initial_states_are_related: *)
      intros ? ? Hinit Hready.
      cbn in *. destruct Hready as (?r_regs & ?r_tl & ?r_inner & ?Hinv). subst.
      unfold counter_related. eexists. split; [|apply Hinv].
      apply IDLE_related.
    - (* initial_state_exists: *)
      intros ? Hready.
      cbn in *. destruct Hready as (?r_regs & ?r_tl & ?r_inner & ?Hinv).
      eexists. split; [reflexivity|].
      unfold counter_related. eexists. split; [|apply Hinv].
      apply IDLE_related.
    - (* nonMMIO_device_step_preserves_state_machine_state: *)
      intros ? ? ? ? ? Ha_valid Hrel.
      (* cbn in sL1, sL2. *)
      (* destruct sL2 as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)). *)
      (* destruct_tl_h2d. destruct_tl_d2h. tlsimpl. subst. *)
      unfold device.run1. unfold counter_device.
      intros Hstep.
      destruct Hrel as [?repr [?Hrel ?Hinv]].
      assert (Hprec: precondition incr (h2d, tt) repr).
      { destruct_tl_h2d. destruct_tl_d2h. tlsimpl.
        cbn in sL1; destruct sL1 as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
        destruct repr as (((?r_state, ?r_regs), ?r_tl), ?r_inner).
        simplify_invariant incr. logical_simplify.
        subst. cbn. ssplit.
        - auto.
        - intros. discriminate.
        - intros. auto.
      }
      eapply incr_invariant_preserved in Hinv as Hinv'; [|reflexivity].
      unfold counter_related. exists (update_repr (c:=incr) (h2d, tt) repr).
      rewrite surjective_pairing with (A:=counter_device) (B:=tl_d2h)
                                      (p:=Semantics.step incr sL1 (h2d, tt)) in Hstep.
      apply pair_equal_spec in Hstep. destruct Hstep as [Hstep1 Hstep2]. subst.
      split; [| apply Hinv'; apply Hprec].
      inversion Hrel; subst;
        destruct_tl_h2d; destruct_tl_d2h; tlsimpl; subst;
          cbn in sL1; destruct sL1 as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
            simplify_invariant incr; logical_simplify; subst;
              cbn -[replace].
      all: try (destruct x as [|[|[|]]]);
        destruct (outstanding_h2d r_tl), d_ready;
        try destruct (TLUL.a_opcode t =? Get)%N, (TLUL.a_opcode t =? PutFullData)%N;
        try (rewrite incrN_word_to_bv);
        boolsimpl; constructor; try assumption.
      all: destruct H6; subst; destruct r_regs; cbn in H |- *; assumption.
    - (* state_machine_read_to_device_read: *)
      (* simpler because device.maxRespDelay=1 *)
      intros ? ? ? ? [v [sH'' Hex_read]] [repr Hrel].
      cbn in Hex_read. logical_simplify. rewrite  H1.
      unfold counter_related.
      match goal with
      | |- context [ device.runUntilResp ?x _ _ ] =>
        remember x as h2d eqn:Eh2d; replace x with h2d
      end.
      assert (Hprec: precondition incr (h2d, tt) repr).
      { destruct_tl_h2d. tlsimpl.
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
        destruct repr as (((?r_state, ?r_regs), ?r_tl), ?r_inner).
        simplify_invariant incr. logical_simplify.
        subst. cbn. ssplit; intros; auto.
      }
      pose (r_ := r). destruct r.
      + (* r=VALUE *)
        pose (sH_ := sH); destruct sH; cbn in H2; try (exfalso; assumption); logical_simplify; subst.
        inversion H; subst.
        eapply runUntilResp_big_step with (s:=sL) in Hprec
          as [n [inputs [sL' [repr' [d2h [sL'' [HrunU [HmaxRespDelay [Einputs [EsL' [Erepr' [Hpostc' [Ed_valid Hinv'']]]]]]]]]]]]]; subst; auto.
        exists d2h, sL'', IDLE.
        ssplit.
        3: cbn; ssplit; try reflexivity; [].
        * assumption.
        * eexists.
          split; [|apply Hinv''].
          simplify_invariant incr.
          simplify_invariant Incr.inner.
          simplify_invariant (tlul_adapter_reg (reg_count:=2)).
          cbn in sL''; destruct sL'' as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
          clear HrunU.
          pose (n_:=n). destruct n as [|[|n]].
          3: unfold device.maxRespDelay, counter_device in HmaxRespDelay; exfalso; lia.
          all: cbn [repeat fold_left] in *.
          -- destruct Hpostc' as [req' [h2d' [regs' [d2h' [io_re' [io_we' [io_address' [io_data' [io_mask' Hpostc']]]]]]]]].
             logical_simplify.
             cbn in H5.
             destruct (outstanding_h2d r_tl) eqn:Houts.
             ++ logical_simplify. rewrite Ed_valid in * |-. discriminate.
             ++ cbn in H5. logical_simplify.
                destruct_tl_d2h. tlsimpl. subst.
                simplify_invariant incr.
                cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
                cbn in Hinv'' |- *.
                rewrite Houts in Hinv'' |- *. cbn in Hinv''. logical_simplify.
                cbn in *.
                logical_simplify. subst.
                rewrite Z_word_N in * by lia. cbn in *. logical_simplify. subst.
                apply IDLE_related.
          -- cbn in Hpostc'.
             destruct (outstanding_h2d r_tl) eqn:Houts;
             destruct Hpostc' as [req' [h2d' [regs' [d2h' [io_re' [io_we' [io_address' [io_data' [io_mask' Hpostc']]]]]]]]];
             logical_simplify;
             cbn in H5; rewrite Houts in H5; cbn in H5; logical_simplify; subst.
             ++ destruct_tl_d2h. tlsimpl. subst.
                simplify_invariant incr.
                cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
                cbn in Hinv'' |- *.
                rewrite Houts in Hinv'' |- *. cbn in Hinv'' |- *. logical_simplify.
                rewrite Houts. cbn.
                rewrite Z_word_N in * by lia. cbn in *.
                destruct H8; subst; apply IDLE_related.
             ++ rewrite Ed_valid in * |-. discriminate.
        * pose (n_:=n). destruct n as [|[|n]].
          -- cbn [repeat fold_left] in *.
             destruct Hpostc' as [req' [h2d' [regs' [d2h' [io_re' [io_we' [io_address' [io_data' [io_mask' Hpostc']]]]]]]]].
             logical_simplify.
             cbn in H5.
             destruct (outstanding_h2d r_tl) eqn:Houts.
             ++ logical_simplify. rewrite Ed_valid in * |-. discriminate.
             ++ cbn in H5. logical_simplify.
                destruct_tl_d2h. tlsimpl. subst.
                simplify_invariant incr.
                cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
                cbn in sL''; destruct sL'' as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
                cbn in Hinv''.
                rewrite Houts in Hinv''. cbn in Hinv''. logical_simplify.
                cbn in *.
                logical_simplify. subst.
                rewrite Z_word_N in * by lia. cbn in *. logical_simplify. subst.
                rewrite H3. apply N_to_word_word_to_N.
          -- cbn [repeat fold_left] in *.
             cbn in Hpostc'.
             destruct (outstanding_h2d r_tl) eqn:Houts;
             destruct Hpostc' as [req' [h2d' [regs' [d2h' [io_re' [io_we' [io_address' [io_data' [io_mask' Hpostc']]]]]]]]];
             logical_simplify;
             cbn in H5; rewrite Houts in H5; cbn in H5; logical_simplify; subst.
             ++ destruct_tl_d2h. tlsimpl. subst.
                simplify_invariant incr.
                cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
                cbn in sL''; destruct sL'' as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
                cbn in Hinv''.
                rewrite Houts in Hinv''. cbn in Hinv''. logical_simplify.
                rewrite Z_word_N in * by lia. cbn -[replace] in *.
                destruct H8; subst; destruct r_regs; cbn in H3 |- *;
                  rewrite H3; apply N_to_word_word_to_N.
             ++ rewrite Ed_valid in * |-. discriminate.
          -- unfold device.maxRespDelay, counter_device in HmaxRespDelay. exfalso. lia.
      + (* r=STATUS *)
        eapply runUntilResp_big_step in Hprec as [n [inputs [sL' [repr' [d2h [sL'' [HrunU [HmaxRespDelay [Einputs [EsL' [Erepr' [Hpostc' [Ed_valid Hinv'']]]]]]]]]]]]]; subst; auto; [|eassumption].
        inversion H; subst.
        * do 3 eexists; ssplit.
          -- rewrite HrunU; reflexivity.
          -- eexists; split; [|eassumption];
               destruct n as [|[|n]];
               [| |unfold device.maxRespDelay, counter_device in HmaxRespDelay; exfalso; lia];
               cbn [repeat fold_left] in *;
               simplify_invariant incr;
               cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
                 logical_simplify; subst;
                   cbn; destruct (outstanding_h2d r_tl) eqn:Eouts;
                     try (cbn; rewrite Eouts; cbn);
                     apply IDLE_related.
          -- cbn. ssplit; try reflexivity.
             destruct n as [|[|n]];
               [| |unfold device.maxRespDelay, counter_device in HmaxRespDelay; exfalso; lia];
               cbn [repeat fold_left] in *; simplify_spec incr;
                 simplify_spec (tlul_adapter_reg (reg_count:=2)).
             ++ destruct Hpostc' as [req' [h2d' [regs' [d2h' [io_re' [io_we' [io_address' [io_data' [io_mask' Hpostc']]]]]]]]]; logical_simplify; cbn in H5;
                  destruct (outstanding_h2d r_tl) eqn:Eouts;
                  [logical_simplify; rewrite Ed_valid in *; discriminate|];
                  cbn in H5; logical_simplify; rewrite H9.
                unfold status_value, STATUS_IDLE, N_to_word, word_to_N.
                simplify_invariant incr.
                cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner)).
                logical_simplify.
                replace (N.to_nat ((N.land (Z.to_N (word.unsigned (word.of_Z 16388))) 4 / 4) mod 1073741824)) with 1.
                ** ZnWords.
                ** ZnWords_pre. rewrite Zmod_small; [|lia].
                   rewrite N.mod_small; cbn; lia.
             ++ admit.
        * admit.
        * admit.
        * admit.
    - (* state_machine_write_to_device_write: *)
      admit.
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
