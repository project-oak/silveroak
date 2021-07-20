Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.ZnWords.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Platform.MetricSane.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.StateMachineMMIOSpec.

Class device_implements_state_machine{word: word.word 32}{mem: map.map word Byte.byte}
      (D: device)(sp: StateMachineSemantics.parameters.parameters 32 word mem) :=
{
  (* the high-level (StateMachineSemantics) layer agrees with the low-level (Cava device)
     layer on what the set of MMIO addresses is *)
  mmioAddrs_match: sameset StateMachineSemantics.parameters.isMMIOAddr device.isMMIOAddr;

  (* simulation relation between high-level states sH and low-level states sL *)
  device_state_related: StateMachineSemantics.parameters.state -> D -> Prop;

  (* "high-level states marked as an initial state"
     = "high-level states related to the device reset state" *)
  initial_state_is_reset_state: forall sH,
      parameters.is_initial_state sH <-> device_state_related sH device.reset_state;

  (* each device state is mapped to at most one state machine state *)
  state_machine_state_unique: forall sL sH1 sH2,
      device_state_related sH1 sL ->
      device_state_related sH2 sL ->
      sH1 = sH2;

  (* transitions that are not responding to MMIO cannot change the state as seen by the software: *)
  nonMMIO_device_step_preserves_state_machine_state:
    forall sL1 sL2 sH ignored_addr ignored_val ignored_resp,
      device_state_related sH sL1 ->
      device.run1 sL1 (false, false, ignored_addr, ignored_val) = (sL2, ignored_resp) ->
      device_state_related sH sL2;

  (* for each high-level read step, if we run the low-level device with the read step's
     address on the input wires, we will get a response after at most device.maxRespDelay
     device cycles, and the response will match the high-level read step's response *)
  state_machine_read_to_device_read: forall n r v sH sH' sL,
      parameters.read_step n sH r v sH' ->
      device_state_related sH sL ->
      exists sL',
        device.runUntilResp true false (word_to_bv (parameters.reg_addr r)) (word_to_bv (word.of_Z 0))
                            device.maxRespDelay sL = (Some (word_to_bv v), sL') /\
        device_state_related sH' sL';

  (* for each high-level write step, if we run the low-level device with the write step's
     address and value on the input wires, we will get an ack response after at most
     device.maxRespDelay device cycles *)
  state_machine_write_to_device_write: forall n r v sH sH' sL,
      parameters.write_step n sH r v sH' ->
      device_state_related sH sL ->
      exists sL' ignored,
        device.runUntilResp false true (word_to_bv (parameters.reg_addr r)) (word_to_bv v)
                            device.maxRespDelay sL = (Some ignored, sL') /\
        device_state_related sH' sL';
}.

Section WithParams.
  Context {word : Interface.word.word 32} {word_ok: word.ok word}
          {Registers: map.map Z word} {Registers_ok: map.ok Registers}
          {mem : Interface.map.map word Byte.byte} {mem_ok: map.ok mem}
          {state_machine_params: StateMachineSemantics.parameters.parameters 32 word mem}
          {state_machine_params_ok: StateMachineSemantics.parameters.ok state_machine_params}
          {D: device}
          {DI: device_implements_state_machine D state_machine_params}.

  Inductive related: MetricRiscvMachine -> ExtraRiscvMachine D -> Prop :=
    mkRelated: forall regs pc npc m xAddrs (t: list LogItem) mc s d,
      execution t s ->
      device_state_related s d ->
      map.undef_on m StateMachineSemantics.parameters.isMMIOAddr ->
      disjoint (of_list xAddrs) StateMachineSemantics.parameters.isMMIOAddr ->
      related
        {| MetricRiscvMachine.getMachine :=
             {| getRegs := regs;
                getPc := pc;
                getNextPc := npc;
                getMem := m;
                getXAddrs := xAddrs;
                getLog := t; |};
           getMetrics := mc; |}
        {| ExtraRiscvMachine.getMachine :=
             {| getRegs := regs;
                getPc := pc;
                getNextPc := npc;
                getMem := m;
                getXAddrs := xAddrs;
                getLog := []; |};
           getExtraState := d |}.

  Definition stepH(initialL: MetricRiscvMachine)(post: MetricRiscvMachine -> Prop): Prop :=
    free.interp MetricMinimalMMIO.interp_action (riscv.Platform.Run.run1 Decode.RV32I)
                initialL (fun _ : unit => post).

  Variable sched: schedule.

  Lemma read_step_isMMIOAddrB: forall n s r v s',
      parameters.read_step n s r v s' ->
      device.isMMIOAddrB (parameters.reg_addr r) n = true.
  Proof.
    intros.
    pose proof (parameters.read_step_size_valid _ _ _ _ _ H) as V. simpl in V.
    pose proof (parameters.read_step_isMMIOAddr _ _ _ _ _ H) as P.
    unfold device.isMMIOAddrB.
    eapply andb_true_intro.
    rewrite !Z.leb_le.
    replace parameters.isMMIOAddr with device.isMMIOAddr in P. 2: {
      symmetry. extensionality x. apply propositional_extensionality. unfold iff.
      pose proof mmioAddrs_match as Q. unfold sameset, subset, elem_of in Q. destruct Q. eauto.
    }
    unfold device.isMMIOAddr in P.
    split.
    - eapply P. lia.
    - enough (word.unsigned (parameters.reg_addr r) + Z.of_nat n - 1 < device.addr_range_pastend).
      1: lia.
      pose proof (parameters.read_step_is_aligned _ _ _ _ _ H) as A.
      specialize (P (word.add (parameters.reg_addr r) (word.of_Z (Z.of_nat n - 1)))).
      ZnWords.
  Qed.

  Lemma write_step_isMMIOAddrB: forall n s r v s',
      parameters.write_step n s r v s' ->
      device.isMMIOAddrB (parameters.reg_addr r) n = true.
  Proof.
    intros.
    pose proof (parameters.write_step_size_valid _ _ _ _ _ H) as V. simpl in V.
    pose proof (parameters.write_step_isMMIOAddr _ _ _ _ _ H) as P.
    unfold device.isMMIOAddrB.
    eapply andb_true_intro.
    rewrite !Z.leb_le.
    replace parameters.isMMIOAddr with device.isMMIOAddr in P. 2: {
      symmetry. extensionality x. apply propositional_extensionality. unfold iff.
      pose proof mmioAddrs_match as Q. unfold sameset, subset, elem_of in Q. destruct Q. eauto.
    }
    unfold device.isMMIOAddr in P.
    split.
    - eapply P. lia.
    - enough (word.unsigned (parameters.reg_addr r) + Z.of_nat n - 1 < device.addr_range_pastend).
      1: lia.
      pose proof (parameters.write_step_is_aligned _ _ _ _ _ H) as A.
      specialize (P (word.add (parameters.reg_addr r) (word.of_Z (Z.of_nat n - 1)))).
      ZnWords.
  Qed.

  (* Uniqueness lemmas follow from device_implements_state_machine, because they say that
     the state machine is behaves like a deterministic Cava device.
     Using this assumption, we can prove uniqueness once and for all, instead of individually
     for each state machine. *)

  Lemma write_step_unique: forall sz prevH prevL r v s s',
      device_state_related prevH prevL ->
      parameters.write_step sz prevH r v s ->
      parameters.write_step sz prevH r v s' ->
      s = s'.
  Proof.
    intros.
    eapply state_machine_write_to_device_write in H0. 2: eassumption.
    eapply state_machine_write_to_device_write in H1. 2: eassumption.
    simp.
    rewrite H0p0 in H1p0. inversion H1p0. subst. clear H1p0.
    eapply state_machine_state_unique; eassumption.
  Qed.

  (* note: could be made stronger by also showing that the read values are equal,
     but we don't need this here *)
  Lemma read_step_unique: forall sz prevH prevL r v s s',
      device_state_related prevH prevL ->
      parameters.read_step sz prevH r v s ->
      parameters.read_step sz prevH r v s' ->
      s = s'.
  Proof.
    intros.
    eapply state_machine_read_to_device_read in H0. 2: eassumption.
    eapply state_machine_read_to_device_read in H1. 2: eassumption.
    simp.
    rewrite H0p0 in H1p0. inversion H1p0. subst. clear H1p0.
    eapply state_machine_state_unique; eassumption.
  Qed.

  Lemma step_unique: forall a prevH prevL args rets s s',
      device_state_related prevH prevL ->
      step a prevH args rets s ->
      step a prevH args rets s' ->
      s = s'.
  Proof.
    unfold step. intros.
    destruct (String.prefix MMIOLabels.WRITE_PREFIX a).
    - simp.
      replace sz0 with sz in *. 2: {
        pose proof (parameters.write_step_size_valid _ _ _ _ _ H0p3) as V1. simpl in V1.
        pose proof (parameters.write_step_size_valid _ _ _ _ _ H1p1) as V2. simpl in V2.
        destruct V1 as [? | [? | [? | ?]]]; destruct V2 as [? | [? | [? | ?]]]; subst;
          reflexivity || discriminate || contradiction.
      }
      eapply parameters.reg_addr_unique in H0p0. subst r1.
      eapply write_step_unique; eassumption.
    - destruct (String.prefix MMIOLabels.READ_PREFIX a). 2: contradiction. simp.
      replace sz0 with sz in *. 2: {
        pose proof (parameters.read_step_size_valid _ _ _ _ _ H0p3) as V1. simpl in V1.
        pose proof (parameters.read_step_size_valid _ _ _ _ _ H1p1) as V2. simpl in V2.
        destruct V1 as [? | [? | [? | ?]]]; destruct V2 as [? | [? | [? | ?]]]; subst;
          reflexivity || discriminate || contradiction.
      }
      eapply parameters.reg_addr_unique in H0p0. subst r0.
      eapply read_step_unique; eassumption.
  Qed.

  Lemma execution_exists_related: forall t sH,
      execution t sH -> exists sL, device_state_related sH sL.
  Proof.
    induction t; cbn; intros.
    - exists device.reset_state. eapply initial_state_is_reset_state. assumption.
    - destruct a as (((mGive & a) & args) & (mReceive & rets)). simp.
      specialize (IHt _ Hp0). destruct IHt as (prevL & IH).
      unfold step in Hp1.
      destruct (String.prefix MMIOLabels.WRITE_PREFIX a).
      + simp. eapply state_machine_write_to_device_write in Hp1p1. 2: eassumption.
        simp. eauto.
      + simp. eapply state_machine_read_to_device_read in Hp1p1. 2: eassumption.
        simp. eauto.
  Qed.

  Lemma execution_unique: forall t s s',
      execution t s -> execution t s' -> s = s'.
  Proof.
    induction t; cbn [execution]; intros.
    - eapply state_machine_state_unique.
      + eapply initial_state_is_reset_state. exact H.
      + eapply initial_state_is_reset_state. exact H0.
    - destruct a as (((mGive & a) & args) & (mReceive & rets)).
      destruct H as (prev & E & St). destruct H0 as (prev' & E' & St').
      specialize (IHt _ _ E E'). subst prev'.
      eapply execution_exists_related in E. simp.
      eapply step_unique; eassumption.
  Qed.

  Lemma bv_to_word_word_to_bv: forall v, bv_to_word (word_to_bv v) = v.
  Proof.
    intros. unfold bv_to_word, word_to_bv.
  Admitted.

  Lemma execution_read_cons: forall n r (v: HList.tuple Byte.byte n) t s1 s2,
      execution t s1 ->
      parameters.read_step n s1 r (word.of_Z (LittleEndian.combine n v)) s2 ->
      execution (MinimalMMIO.mmioLoadEvent (W := mkWords) (parameters.reg_addr r) v :: t) s2.
  Proof. intros. eapply execution_step_read; eauto. Qed.

  Lemma execution_write_cons: forall n r (v: HList.tuple Byte.byte n) t s1 s2,
      execution t s1 ->
      parameters.write_step n s1 r (word.of_Z (LittleEndian.combine n v)) s2 ->
      execution (MinimalMMIO.mmioStoreEvent (W := mkWords) (parameters.reg_addr r) v :: t) s2.
  Proof. intros. eapply execution_step_write; eauto. Qed.

  Lemma preserve_undef_on_unchecked: forall sz (m: mem) a v1 v2 s,
      Memory.load_bytes sz m a = Some v1 ->
      map.undef_on m s ->
      map.undef_on (Memory.unchecked_store_bytes sz m a v2) s.
  Proof.
    intros.
    refine (MinimalMMIO.preserve_undef_on _ _ _ _ _ _ _ H0).
    unfold Memory.store_bytes.
    match goal with
    | |- match ?x with _ => _ end = _ => replace x with (Some v1)
    end.
    1: reflexivity.
    symmetry. exact H.
  Qed.

  Lemma preserve_disjoint_of_invalidateXAddrs: forall sz xAddrs a s,
      disjoint (of_list xAddrs) s ->
      disjoint (of_list (Primitives.invalidateWrittenXAddrs sz a xAddrs)) s.
  Proof.
    induction sz; intros; cbn.
    - assumption.
    - change removeXAddr with (@List.removeb word word.eqb _).
      rewrite ?ListSet.of_list_removeb.
      eauto 10 using disjoint_diff_l.
  Qed.

  Lemma stateMachine_primitive_to_cava: forall (initialH: MetricRiscvMachine) (p: riscv_primitive)
      (postH: primitive_result p -> MetricRiscvMachine -> Prop),
      MetricMinimalMMIO.interp_action p initialH postH ->
      forall (initialL: ExtraRiscvMachine D),
        related initialH initialL ->
        exists finalH res finalL,
          InternalMMIOMachine.interpret_action p initialL = (Some res, finalL) /\
          postH res finalH /\
          related finalH finalL.
  Proof.
    intros. inversion H0. clear H0. subst.
    destruct p;
      cbn -[HList.tuple Memory.load_bytes Primitives.invalidateWrittenXAddrs] in *; try contradiction.

    (* GetRegister *)
    { destruct (Z.eq_dec z 0). 1: eauto 10 using mkRelated.
      cbn. destruct (map.get regs z); eauto 10 using mkRelated. }

    (* SetRegister *)
    { destruct (Z.eq_dec z 0). 1: eauto 10 using mkRelated.
      unfold Monads.OStateOperations.put. cbn. eauto 10 using mkRelated. }

    (* Load* *)
    1-4: unfold MinimalMMIO.load, MinimalMMIO.nonmem_load in H;
      destruct H as [HX HL]; cbn -[HList.tuple Memory.load_bytes] in *.
    1-4: match type of HL with
         | match ?x with _ => _ end => destruct x eqn: E; [destruct s0|]
         end;
         try specialize (HX eq_refl);
         rewrite ?(isXAddr4B_true _ _ HX);
         eauto 10 using mkRelated.
    1-4: simp; erewrite ?read_step_isMMIOAddrB by eassumption.
    1-4: match goal with
         | E1: execution _ _, E2: execution _ _ |- _ =>
           pose proof (execution_unique _ _ _ E1 E2); subst; clear E2
         end.
    1-4: edestruct state_machine_read_to_device_read as (d' & RU & Rel'); [eassumption..|].
    1-4: cbn -[HList.tuple]; rewrite RU; cbn -[HList.tuple].
    4: { (* 64-bit MMIO is not supported: *)
      eapply parameters.read_step_size_valid in HLp2p2. simpl in HLp2p2. exfalso. intuition congruence.
    }
    1-3: rewrite bv_to_word_word_to_bv;
         rewrite word.unsigned_of_Z_nowrap by (pose proof (LittleEndian.combine_bound v); lia);
         rewrite LittleEndian.split_combine.
    1-3: eauto 15 using mkRelated, execution_read_cons.

    (* Store* *)
    1-4: unfold MinimalMMIO.store, MinimalMMIO.nonmem_store, Memory.store_bytes in *;
      cbn -[HList.tuple Memory.load_bytes Memory.unchecked_store_bytes
            Primitives.invalidateWrittenXAddrs] in *.
    1-4: match type of H with
         | match match ?x with _ => _ end with _ => _ end => destruct x eqn: E
         end.
    1-8: unfold Monads.OStateOperations.put;
         cbn -[HList.tuple Memory.load_bytes Memory.unchecked_store_bytes
               Primitives.invalidateWrittenXAddrs] in *;
         eauto 15 using mkRelated, preserve_undef_on_unchecked, preserve_disjoint_of_invalidateXAddrs.
    1-4: simp.
    1-4: match goal with
         | H: parameters.write_step _ _ _ _ _ |- _ =>
           rename H into WS; pose proof WS as WS';
           eapply parameters.write_step_size_valid in WS';
           simpl in WS'; destruct WS' as [? | [? | [? | ?]]];
           try contradiction; try subst sz; try discriminate (* <- also gets rid of 8-byte MMIO case *)
         end.
    1-3: simp; erewrite write_step_isMMIOAddrB by eassumption.
    1-3: match goal with
         | E1: execution _ _, E2: execution _ _ |- _ =>
           pose proof (execution_unique _ _ _ E1 E2); subst; clear E2
         end.
    1-3: edestruct state_machine_write_to_device_write as (d' & ignored & RU & Rel'); [eassumption..|].
    1-3: cbn -[HList.tuple Primitives.invalidateWrittenXAddrs]; rewrite RU;
         cbn -[HList.tuple Primitives.invalidateWrittenXAddrs].
    1-3: eauto 15 using mkRelated, execution_write_cons, preserve_disjoint_of_invalidateXAddrs.

    (* GetPC *)
    { eauto 10 using mkRelated. }

    (* SetPC *)
    { unfold Monads.OStateOperations.put. eauto 10 using mkRelated. }

    (* EndCycleNormal *)
    { unfold Monads.OStateOperations.put. eauto 10 using mkRelated. }
  Qed.

  Lemma stateMachine_free_to_cava{A: Type}:
    forall (p: free riscv_primitive primitive_result A) (initialH: MetricRiscvMachine)
      (postH: A -> MetricRiscvMachine -> Prop),
      free.interp MetricMinimalMMIO.interp_action p initialH postH ->
      forall (initialL: ExtraRiscvMachine D),
        related initialH initialL ->
        exists finalH res finalL,
          free.interp_as_OState InternalMMIOMachine.interpret_action p initialL =
            (Some res, finalL) /\
          postH res finalH /\
          related finalH finalL.
  Proof.
    induction p; intros.
    - simpl in H0. eapply stateMachine_primitive_to_cava in H0. 2: eassumption. simp.
      simpl. rewrite H0p0. eapply H; eassumption.
    - simpl in *. eauto 10.
  Qed.

  Lemma nonMMIO_device_steps_preserve_state_machine_state: forall n initialH initialL,
      related initialH initialL ->
      exists finalL, device_steps n initialL = (Some tt, finalL) /\
                     related initialH finalL.
  Proof.
    induction n; simpl; intros.
    - eauto.
    - eapply IHn. inversion H. subst. clear H. cbn.
      unfold device_step_without_IO.
      econstructor.
      + eassumption.
      + match goal with
        | |- context[fst ?p] => destruct p eqn: E
        end.
        eapply nonMMIO_device_step_preserves_state_machine_state. 1: eassumption.
        simpl.
        exact E.
      + assumption.
      + assumption.
  Qed.

  Lemma stateMachine_to_cava_1: forall (initialH: MetricRiscvMachine) (initialL: ExtraRiscvMachine D)
                                       steps_done post,
      related initialH initialL ->
      stepH initialH post ->
      exists finalL finalH, nth_step sched steps_done initialL = (Some tt, finalL) /\
                            related finalH finalL /\
                            post finalH.
  Proof.
    intros.
    unfold stepH in H0.
    unfold nth_step.
    unfold Monads.Bind, Monads.OState_Monad.
    destruct (nonMMIO_device_steps_preserve_state_machine_state (sched steps_done) _ _ H)
      as (initialL' & E & R').
    rewrite E.
    eapply stateMachine_free_to_cava in H0. 2: exact R'.
    simp. destruct res. eauto.
  Qed.

  Lemma stateMachine_to_cava: forall (initialH: MetricRiscvMachine) (initialL: ExtraRiscvMachine D)
                                     steps_done post,
      related initialH initialL ->
      runsTo stepH initialH post ->
      exists steps_remaining finalL finalH,
        run_rec sched steps_done steps_remaining initialL = (Some tt, finalL) /\
        related finalH finalL /\
        post finalH.
  Proof.
    intros. revert initialL steps_done H. induction H0; intros.
    - exists 0%nat. unfold run, run_rec, Monads.Return. simpl. eauto.
    - pose proof stateMachine_to_cava_1 as One.
      specialize One with (1 := H2) (2 := H). specialize (One steps_done).
      destruct One as (midL & midH & One & Rmid & M).
      specialize H1 with (1 := M) (2 := Rmid). specialize (H1 (S steps_done)).
      destruct H1 as (steps_remaining & finalL & finalH & Star & Rfinal & Pfinal).
      exists (S steps_remaining). simpl. rewrite One. eauto.
  Qed.

End WithParams.
