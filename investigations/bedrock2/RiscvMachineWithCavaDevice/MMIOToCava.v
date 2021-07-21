Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Strings.String. Open Scope string_scope.
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

  (* if an initial high-level state is related to some low-level state, it must be a ready state *)
  initial_state_is_ready_state: forall sH sL,
      parameters.is_initial_state sH ->
      device_state_related sH sL ->
      device.is_ready_state sL;

  (* every initial high-level state is related to every initial low-level state *)
  initial_states_are_related: forall sH sL,
      parameters.is_initial_state sH ->
      device.is_ready_state sL ->
      device_state_related sH sL;

  (* for every initial low-level state, there exists a related initial high-level state *)
  initial_state_exists: forall sL,
      device.is_ready_state sL ->
      exists sH, parameters.is_initial_state sH /\ device_state_related sH sL;

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
    mkRelated: forall regs pc npc m xAddrs (t: list LogItem) mc d,
      (forall s, execution t s -> device_state_related s d) ->
      (exists s, execution t s /\ device_state_related s d) ->
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

  Lemma rerun_read_step: forall sz t d d' r v,
      (forall s, execution t s -> device_state_related s d) ->
      device.runUntilResp true false (word_to_bv (parameters.reg_addr r))
                          (word_to_bv (word.of_Z 0)) device.maxRespDelay d =
      (Some (word_to_bv (word.of_Z (LittleEndian.combine sz v))), d') ->
      In sz [1%nat; 2%nat; 4%nat] ->
      forall s,
        execution (MinimalMMIO.mmioLoadEvent (parameters.reg_addr r) v :: t) s ->
        device_state_related s d'.
  Proof.
    intros. destruct H2 as (s'' & Ex & St).
    unfold step in St.
    simpl in H1. destruct H1 as [H1 | [H1 | [H1 | []]]]; subst;
    destruct St as (r' & val & sz & A & B & C & F);
    eapply parameters.reg_addr_unique in A; subst.
    all: edestruct state_machine_read_to_device_read as (d'' & RU'' & Rel'');
      [exact F|eapply H; exact Ex|].
    all: rewrite H0 in RU''; inversion RU''; subst; assumption.
  Qed.

  Lemma rerun_write_step: forall sz t d d' r v ignored,
      (forall s, execution t s -> device_state_related s d) ->
      device.runUntilResp false true (word_to_bv (parameters.reg_addr r))
                          (word_to_bv (word.of_Z (LittleEndian.combine sz v))) device.maxRespDelay d =
      (Some ignored, d') ->
      In sz [1%nat; 2%nat; 4%nat] ->
      forall s,
        execution (MinimalMMIO.mmioStoreEvent (parameters.reg_addr r) v :: t) s ->
        device_state_related s d'.
  Proof.
    intros. destruct H2 as (s'' & Ex & St).
    unfold step in St.
    simpl in H1. destruct H1 as [H1 | [H1 | [H1 | []]]]; subst;
    destruct St as (r' & sz & A & B & C & F);
    eapply parameters.reg_addr_unique in A; subst.
    all: edestruct state_machine_write_to_device_write as (d'' & ignored'' & RU'' & Rel'');
      [exact F|eapply H; exact Ex|];
      pose proof (eq_trans (eq_sym H0) RU'') as E; inversion E; assumption.
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
         | match ?x with _ => _ end => destruct x eqn: E; [destruct s|]
         end;
         try specialize (HX eq_refl);
         rewrite ?(isXAddr4B_true _ _ HX);
         eauto 10 using mkRelated.
    1-4: simp; erewrite ?read_step_isMMIOAddrB by eassumption.
    1-4: edestruct state_machine_read_to_device_read as (d' & RU & Rel'); [eassumption|solve[eauto]|].
    1-4: cbn -[HList.tuple]; rewrite RU; cbn -[HList.tuple].
    4: { (* 64-bit MMIO is not supported: *)
      eapply parameters.read_step_size_valid in HLp2p2. simpl in HLp2p2. exfalso. intuition congruence.
    }
    1-3: rewrite bv_to_word_word_to_bv;
         rewrite word.unsigned_of_Z_nowrap by (pose proof (LittleEndian.combine_bound v); lia);
         rewrite LittleEndian.split_combine.
    1-3: eauto 20 using mkRelated, execution_read_cons, rerun_read_step, in_eq, in_cons.

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
    1-3: edestruct state_machine_write_to_device_write as (d' & ignored & RU & Rel');
           [eassumption|solve[eauto]|].
    1-3: cbn -[HList.tuple Primitives.invalidateWrittenXAddrs]; rewrite RU;
         cbn -[HList.tuple Primitives.invalidateWrittenXAddrs].
    1-3: eauto 15 using mkRelated, execution_write_cons, preserve_disjoint_of_invalidateXAddrs,
         rerun_write_step, in_eq, in_cons.

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
      eapply mkRelated.
      + intros.
        match goal with
        | |- context[fst ?p] => destruct p eqn: E
        end.
        eapply nonMMIO_device_step_preserves_state_machine_state. 1: eauto.
        simpl.
        exact E.
      + match goal with
        | |- context[fst ?p] => destruct p eqn: E
        end.
        rename s into d'.
        destruct H1 as (s' & Ex & Rel).
        simpl.
        eexists. split; [eassumption|].
        eapply nonMMIO_device_step_preserves_state_machine_state; eassumption.
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
