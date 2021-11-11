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
      (D: device)(M: state_machine.parameters) :=
{
  (* the high-level (StateMachineSemantics) layer agrees with the low-level (Cava device)
     layer on what the set of MMIO addresses is *)
  mmioAddrs_match: sameset state_machine.isMMIOAddr device.isMMIOAddr;

  (* simulation relation between high-level states sH and low-level states sL *)
  device_state_related: state_machine.state -> D -> Prop;

  (* if an initial high-level state is related to some low-level state, it must be a ready state *)
  initial_state_is_ready_state: forall sH sL,
      state_machine.is_initial_state sH ->
      device_state_related sH sL ->
      device.is_ready_state sL;

  (* every initial high-level state is related to every initial low-level state *)
  initial_states_are_related: forall sH sL,
      state_machine.is_initial_state sH ->
      device.is_ready_state sL ->
      device_state_related sH sL;

  (* for every initial low-level state, there exists a related initial high-level state *)
  initial_state_exists: forall sL,
      device.is_ready_state sL ->
      exists sH, state_machine.is_initial_state sH /\ device_state_related sH sL;

  (* transitions that are not responding to MMIO cannot change the state as seen by the software: *)
  nonMMIO_device_step_preserves_state_machine_state:
    forall sL1 sL2 sH h2d ignored_resp,
      a_valid h2d = false ->
      device_state_related sH sL1 ->
      device.run1 sL1 h2d = (sL2, ignored_resp) ->
      device_state_related sH sL2;

  (* for each high-level state sH from which n bytes can be read at register r,
     if we run the low-level device with the read step's address on the input wires,
     it either tells us to try again later (but by decreasing device.maxRespDelay,
     it promises that it won't keep telling us to try again later forever), or
     we will get a response matching some possible high-level read step's response,
     but not necessarily the one we used to show that sH accepts reads (to allow
     underspecification-nondeterminism in the high-level state machine) *)

  (* TODO: replace the length clauses with [In (a_source h2d) (device.tl_inflight_ops sL)] *)
  state_machine_read_to_device_read_or_later: forall log2_nbytes r sH sL sL' h2d d2h,
      (exists v sH', state_machine.read_step (2 ^ log2_nbytes) sH r v sH') ->
      device_state_related sH sL ->
      a_valid h2d = true ->
      a_opcode h2d = Get ->
      a_size h2d = N.of_nat log2_nbytes ->
      a_address h2d = word_to_N (state_machine.reg_addr r) ->
      d_ready h2d = true ->
      List.length (device.tl_inflight_ops sL) = 0%nat ->
      device.run1 sL h2d = (sL', d2h) ->
      if a_ready (device.last_d2h sL) then
        if d_valid d2h then
          exists sH',
            device_state_related sH' sL' /\
            state_machine.read_step (2 ^ log2_nbytes) sH r (N_to_word (d_data d2h)) sH' /\
            List.length (device.tl_inflight_ops sL') = 0%nat
        else
          device_state_related sH sL' /\
          (device.maxRespDelay sL' (set_d_ready true tl_h2d_default) < device.maxRespDelay sL h2d)%nat /\
          List.length (device.tl_inflight_ops sL') = 1%nat
      else
        device_state_related sH sL' /\
        (device.maxRespDelay sL' h2d < device.maxRespDelay sL h2d)%nat /\
        List.length (device.tl_inflight_ops sL') = 0%nat;

  state_machine_read_to_device_read_or_later_wait: forall log2_nbytes r sH sL sL' d2h,
      (exists v sH', state_machine.read_step (2 ^ log2_nbytes) sH r v sH') ->
      device_state_related sH sL ->
      List.length (device.tl_inflight_ops sL) = 1%nat ->
      device.run1 sL (set_d_ready true tl_h2d_default) = (sL', d2h) ->
      if d_valid d2h then
        exists sH',
          device_state_related sH' sL' /\
          state_machine.read_step (2 ^ log2_nbytes) sH r (N_to_word (d_data d2h)) sH' /\
          List.length (device.tl_inflight_ops sL') = 0%nat
      else
        device_state_related sH sL' /\
        (device.maxRespDelay sL' (set_d_ready true tl_h2d_default) < device.maxRespDelay sL (set_d_ready true tl_h2d_default))%nat /\
        List.length (device.tl_inflight_ops sL') = 1%nat;

  (* for each high-level state sH in which an n-byte write to register r with value v is possible,
     if we run the low-level device with the write step's address and value on the input wires,
     it either tells us to try again later (but by decreasing device.maxRespDelay,
     it promises that it won't keep telling us to try again later forever), or
     we will get an ack response and the device will end up in a state corresponding to a
     high-level state reached after a high-level write, but not necessarily in the state
     we used to show that sH accepts writes *)
  state_machine_write_to_device_write_or_later: forall log2_nbytes r v sH sL sL' h2d d2h,
      (exists sH', state_machine.write_step (2 ^ log2_nbytes) sH r v sH') ->
      device_state_related sH sL ->
      a_valid h2d = true ->
      a_opcode h2d = PutFullData ->
      a_size h2d = N.of_nat log2_nbytes ->
      a_address h2d = word_to_N (state_machine.reg_addr r) ->
      a_data h2d = word_to_N v ->
      d_ready h2d = true ->
      List.length (device.tl_inflight_ops sL) = 0%nat ->
      device.run1 sL h2d = (sL', d2h) ->
      if a_ready (device.last_d2h sL) then
        if d_valid d2h then
          exists sH',
            device_state_related sH' sL' /\
            state_machine.write_step (2 ^ log2_nbytes) sH r v sH' /\
            List.length (device.tl_inflight_ops sL') = 0%nat
        else
          device_state_related sH sL' /\
          (device.maxRespDelay sL' h2d < device.maxRespDelay sL h2d)%nat /\
          List.length (device.tl_inflight_ops sL') = 1%nat
      else
        device_state_related sH sL' /\
        (device.maxRespDelay sL' h2d < device.maxRespDelay sL h2d)%nat /\
        List.length (device.tl_inflight_ops sL') = 0%nat;

  state_machine_write_to_device_write_or_later_wait: forall log2_nbytes r v sH sL sL' h2d d2h,
      (exists sH', state_machine.write_step (2 ^ log2_nbytes) sH r v sH') ->
      device_state_related sH sL ->
      d_ready h2d = true ->
      List.length (device.tl_inflight_ops sL) = 1%nat ->
      device.run1 sL h2d = (sL', d2h) ->
      if d_valid d2h then
        exists sH',
          device_state_related sH' sL' /\
          state_machine.write_step (2 ^ log2_nbytes) sH r v sH' /\
          List.length (device.tl_inflight_ops sL') = 0%nat
      else
        device_state_related sH sL' /\
        (device.maxRespDelay sL' h2d < device.maxRespDelay sL h2d)%nat /\
        List.length (device.tl_inflight_ops sL') = 1%nat;

  (* If two steps starting in the same high-level state agree on what gets appended to the trace,
     then the resulting high-level states must be equal.
     Note that this is a property purely about the high-level state machine that does not involve
     the low-level device.
     This restriction still allows external nondeterminism (ie nondeterminism that immediately shows
     up in the trace) in the high-level state machine, but disallows internal nondeterminism
     that might never or only later be observable in the trace. *)
  read_step_unique: forall n r v sH sH' sH'',
      state_machine.read_step n r v sH sH' ->
      state_machine.read_step n r v sH sH'' ->
      sH' = sH'';
  write_step_unique: forall n r v sH sH' sH'',
      state_machine.write_step n r v sH sH' ->
      state_machine.write_step n r v sH sH'' ->
      sH' = sH'';

  (* In order for execution_unique, we also require that there's only one initial high-level state *)
  initial_state_unique: forall sH sH',
      state_machine.is_initial_state sH -> state_machine.is_initial_state sH' -> sH = sH';
}.

Section WithParams.
  Context {word : Interface.word.word 32} {word_ok: word.ok word}
          {Registers: map.map Z word} {Registers_ok: map.ok Registers}
          {mem : Interface.map.map word Byte.byte} {mem_ok: map.ok mem}
          {M: state_machine.parameters} {M_ok: state_machine.ok M}
          {D: device}
          {DI: device_implements_state_machine D M}.

  (* for each high-level state sH from which n bytes can be read at register r,
     if we run the low-level device with the read step's address on the input wires,
     we will get a response after at most device.maxRespDelay device cycles,
     and the response will match some possible high-level read step's response,
     but not necessarily the one we used to show that sH accepts reads (to allow
     underspecification-nondeterminism in the high-level state machine) *)
  Lemma state_machine_read_to_device_read_wait: forall log2_nbytes r sH sL,
      (exists v sH', state_machine.read_step (2 ^ log2_nbytes) sH r v sH') ->
      device_state_related sH sL ->
      List.length (device.tl_inflight_ops sL) = 1%nat ->
      exists d2h sL' sH',
        device.waitForResp (device.maxRespDelay sL (set_d_ready true tl_h2d_default)) sL = (Some d2h, sL') /\
        device_state_related sH' sL' /\
        state_machine.read_step (2 ^ log2_nbytes) sH r (N_to_word (d_data d2h)) sH' /\
        List.length (device.tl_inflight_ops sL') = 0%nat.
  Proof.
    intros. remember (device.maxRespDelay sL (set_d_ready true tl_h2d_default)) as fuel.
    remember (S fuel) as B.
    assert (device.maxRespDelay sL (set_d_ready true tl_h2d_default) <= fuel < B)%nat as HB by lia.
    clear HeqB Heqfuel.
    revert fuel sH sL H H0 H1 HB.
    induction B; intros.
    - exfalso. lia.
    - destr fuel; cbn [device.waitForResp]; destruct_one_match;
        pose proof (state_machine_read_to_device_read_or_later_wait
                      _ _ _ _ _ _ H H0 H1 E) as P;
        destruct_one_match.
      + destruct P as (sH' & R & V & L). eauto 10.
      + exfalso. lia.
      + destruct P as (sH' & R & V & L). eauto 10.
      + destruct P as (R & Decl & L).
        edestruct IHB as (d2h & sL'' & sH'' & Run & Rel & St & Ln);
          try eassumption. 2: eauto 10. lia.
  Qed.

  Lemma waitForResp_mono : forall (fuel fuel' : nat) s d2h s',
      (fuel <= fuel')%nat ->
      device.waitForResp fuel s = (Some d2h, s') ->
      device.waitForResp fuel' s = (Some d2h, s').
  Proof.
    intros ? ?. revert fuel. induction fuel'; intros; inversion H; subst; auto.
    cbn [device.waitForResp].
    destruct_one_match. destruct_tl_d2h. tlsimpl.
    destruct d_valid.
    - destruct fuel; cbn in H0; rewrite E in H0; cbn in H0; assumption.
    - destruct fuel; cbn in H0; rewrite E in H0; cbn in H0; try discriminate.
      eapply IHfuel' with (fuel:=fuel); auto. lia.
  Qed.

  Lemma state_machine_read_to_device_read: forall log2_nbytes r sH sL h2d,
      (exists v sH', state_machine.read_step (2 ^ log2_nbytes) sH r v sH') ->
      device_state_related sH sL ->
      a_valid h2d = true ->
      a_opcode h2d = Get ->
      a_size h2d = N.of_nat log2_nbytes ->
      a_address h2d = word_to_N (state_machine.reg_addr r) ->
      d_ready h2d = true ->
      List.length (device.tl_inflight_ops sL) = 0%nat ->
      exists d2h sL' sH',
        device.runUntilResp h2d (device.maxRespDelay sL h2d) sL = (Some d2h, sL') /\
        device_state_related sH' sL' /\
        state_machine.read_step (2 ^ log2_nbytes) sH r (N_to_word (d_data d2h)) sH' /\
        List.length (device.tl_inflight_ops sL') = 0%nat.
  Proof.
    intros. remember (device.maxRespDelay sL h2d) as fuel. remember (S fuel) as B.
    assert (device.maxRespDelay sL h2d <= fuel < B)%nat as HB by lia. clear HeqB Heqfuel.
    revert fuel sH sL H H0 HB H6.
    induction B; intros.
    - exfalso. lia.
    - destr fuel; cbn [device.runUntilResp]; destruct_one_match;
          pose proof (state_machine_read_to_device_read_or_later
                        _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5 H6 E) as P;
          repeat destruct_one_match.
      + (* 0 remaining fuel, device ready, valid response: *)
        destruct P as (sH' & R & V & L). eauto 10.
      + (* 0 remaining fuel, device ready, no valid response: *)
        destruct P as (R & Decr & L). exfalso. lia.
      + (* 0 remaining fuel, device not ready: *)
        destruct P as (R & Decr & L). exfalso. lia.

      + (* some remaining fuel, device ready, valid response: *)
        destruct P as (sH' & R & V & L). eauto 10.
      + (* some remaining fuel, device ready, no valid response: *)
        destruct P as (R & Decr & L).
        pose proof (state_machine_read_to_device_read_wait
                      _ _ _ _ H R L) as (d2h & sL'' & sH'' & W' & R' & V' & L').
        eapply waitForResp_mono in W'. 1: eauto 10. lia.
      + (* some remaining fuel, device not ready: *)
        destruct P as (R & Decr & L).
        edestruct IHB as (d2h & sL'' & sH'' & Run & Rel & St);
          try eassumption. 2: eauto 10. lia.
  Qed.

  (* for each high-level state sH in which an n-byte write to register r with value v is possible,
     if we run the low-level device with the write step's address and value on the input wires,
     we will get an ack response after at most device.maxRespDelay device cycles,
     and the device will end up in a state corresponding to a high-level state reached after
     a high-level write, but not necessarily in the state we used to show that sH accepts writes *)
  Lemma state_machine_write_to_device_write: forall log2_nbytes r v sH sL h2d,
      (exists sH', state_machine.write_step (2 ^ log2_nbytes) sH r v sH') ->
      device_state_related sH sL ->
      a_valid h2d = true ->
      a_opcode h2d = PutFullData ->
      a_size h2d = N.of_nat log2_nbytes ->
      a_address h2d = word_to_N (state_machine.reg_addr r) ->
      a_data h2d = word_to_N v ->
      d_ready h2d = true ->
      exists ignored sL' sH',
        device.runUntilResp h2d (device.maxRespDelay sL h2d) sL = (Some ignored, sL') /\
        device_state_related sH' sL' /\
        state_machine.write_step (2 ^ log2_nbytes) sH r v sH'.
  Proof.
    intros. remember (device.maxRespDelay sL h2d) as fuel. remember (S fuel) as B.
    assert (device.maxRespDelay sL h2d <= fuel < B)%nat as HB by lia. clear HeqB Heqfuel.
    revert fuel sH sL H H0 HB.
    induction B; intros.
    - exfalso. lia.
    - destr fuel; cbn [device.runUntilResp]; destruct_one_match;
        pose proof (state_machine_write_to_device_write_or_later
                      _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5 H6 E) as P;
        (destruct_one_match; [destruct P as (sH' & R & V) | destruct P as (R & Decr)]).
      + (* 0 remaining fuel, valid response: *)
        clear -R V. eauto 10.
      + (* 0 remaining fuel, no valid response: *)
        exfalso. lia.
      + (* some remaining fuel, valid response: *)
        clear -R V. eauto 10.
      + (* some remaining fuel, no valid response *)
        edestruct IHB as (d2h & sL'' & sH'' & Run & Rel & St).
        1: eassumption. 1: exact R. 2: eauto 10. lia.
  Qed.

  Inductive related: MetricRiscvMachine -> ExtraRiscvMachine D -> Prop :=
    mkRelated: forall regs pc npc m xAddrs (t: list LogItem) t_ignored mc d s,
      execution t s ->
      device_state_related s d ->
      map.undef_on m state_machine.isMMIOAddr ->
      disjoint (of_list xAddrs) state_machine.isMMIOAddr ->
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
                getLog := t_ignored; (* we don't use the log of the low-level machine *) |};
           getExtraState := d |}.

  Definition stepH(initialL: MetricRiscvMachine)(post: MetricRiscvMachine -> Prop): Prop :=
    free.interp MetricMinimalMMIO.interp_action (riscv.Platform.Run.run1 Decode.RV32IM)
                initialL (fun _ : unit => post).

  Variable sched: schedule.

  Lemma read_step_isMMIOAddrB: forall n s r v s',
      state_machine.read_step n s r v s' ->
      device.isMMIOAddrB (state_machine.reg_addr r) n = true.
  Proof.
    intros.
    pose proof (state_machine.read_step_size_valid _ _ _ _ _ H) as V. simpl in V.
    pose proof (state_machine.read_step_isMMIOAddr _ _ _ _ _ H) as P.
    unfold device.isMMIOAddrB.
    eapply andb_true_intro.
    rewrite !Z.leb_le.
    replace state_machine.isMMIOAddr with device.isMMIOAddr in P. 2: {
      symmetry. extensionality x. apply propositional_extensionality. unfold iff.
      pose proof mmioAddrs_match as Q. unfold sameset, subset, elem_of in Q. destruct Q. eauto.
    }
    unfold device.isMMIOAddr in P.
    split.
    - eapply P. lia.
    - enough (word.unsigned (state_machine.reg_addr r) + Z.of_nat n - 1 < device.addr_range_pastend).
      1: lia.
      pose proof (state_machine.read_step_is_aligned _ _ _ _ _ H) as A.
      specialize (P (word.add (state_machine.reg_addr r) (word.of_Z (Z.of_nat n - 1)))).
      ZnWords.
  Qed.

  Lemma write_step_isMMIOAddrB: forall n s r v s',
      state_machine.write_step n s r v s' ->
      device.isMMIOAddrB (state_machine.reg_addr r) n = true.
  Proof.
    intros.
    pose proof (state_machine.write_step_size_valid _ _ _ _ _ H) as V. simpl in V.
    pose proof (state_machine.write_step_isMMIOAddr _ _ _ _ _ H) as P.
    unfold device.isMMIOAddrB.
    eapply andb_true_intro.
    rewrite !Z.leb_le.
    replace state_machine.isMMIOAddr with device.isMMIOAddr in P. 2: {
      symmetry. extensionality x. apply propositional_extensionality. unfold iff.
      pose proof mmioAddrs_match as Q. unfold sameset, subset, elem_of in Q. destruct Q. eauto.
    }
    unfold device.isMMIOAddr in P.
    split.
    - eapply P. lia.
    - enough (word.unsigned (state_machine.reg_addr r) + Z.of_nat n - 1 < device.addr_range_pastend).
      1: lia.
      pose proof (state_machine.write_step_is_aligned _ _ _ _ _ H) as A.
      specialize (P (word.add (state_machine.reg_addr r) (word.of_Z (Z.of_nat n - 1)))).
      ZnWords.
  Qed.

  Lemma execution_unique: forall t s s',
      execution t s -> execution t s' -> s = s'.
  Proof.
    eapply StateMachineProperties.execution_unique.
    - exact initial_state_unique.
    - exact read_step_unique.
    - exact write_step_unique.
  Qed.

  Lemma execution_read_cons: forall n r (v: HList.tuple Byte.byte n) t s1 s2,
      execution t s1 ->
      state_machine.read_step n s1 r (word.of_Z (LittleEndian.combine n v)) s2 ->
      execution (MinimalMMIO.mmioLoadEvent (state_machine.reg_addr r) v :: t) s2.
  Proof. intros. eapply execution_step_read; eauto. Qed.

  Lemma execution_write_cons: forall n r (v: HList.tuple Byte.byte n) t s1 s2,
      execution t s1 ->
      state_machine.write_step n s1 r (word.of_Z (LittleEndian.combine n v)) s2 ->
      execution (MinimalMMIO.mmioStoreEvent (state_machine.reg_addr r) v :: t) s2.
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
    - change removeXAddr with (@List.removeb word word.eqb).
      rewrite ?ListSet.of_list_removeb.
      eauto 10 using disjoint_diff_l.
  Qed.

  Lemma combine_split_read_step: forall n s r v s',
      state_machine.read_step n s r v s' ->
      state_machine.read_step n s r
        (word.of_Z (LittleEndian.combine n (LittleEndian.split n (word.unsigned v)))) s'.
  Proof.
    intros.
    rewrite LittleEndian.combine_split.
    rewrite Z.mod_small. 2: {
      split.
      - eapply word.unsigned_range.
      - eapply state_machine.read_step_bounded. eassumption.
    }
    rewrite word.of_Z_unsigned.
    assumption.
  Qed.

  Lemma Z_word_N : forall n w,
      (n <= 4)%nat ->
      word_to_N (word.of_Z (LittleEndian.combine n w)) =
      BinIntDef.Z.to_N (LittleEndian.combine n w).
  Proof.
    intros. unfold word_to_N. rewrite word.unsigned_of_Z_nowrap.
    - reflexivity.
    - split.
      + apply LittleEndian.combine_bound.
      + eapply Z.lt_le_trans.
        * apply LittleEndian.combine_bound.
        * apply Z.pow_le_mono_r; lia.
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
    1-4: match goal with
         | |- context[device.runUntilResp ?p _ _] =>
           edestruct state_machine_read_to_device_read with (h2d := p)
             as (v'' & d'' & s'' & RU'' & Rel'' & RS'');
             [do 2 eexists; match goal with
                            | H: state_machine.read_step ?n _ _ _ _ |- _ =>
                              change n at 1 with (2 ^ (Nat.log2 n))%nat in H
                            end; eassumption|eassumption|reflexivity..|]
         end.
    1-4: cbn -[HList.tuple]; tlsimpl; simpl in RU''; rewrite RU''; cbn -[HList.tuple].
    4: { (* 64-bit MMIO is not supported: *)
      eapply state_machine.read_step_size_valid in HLp2p2. simpl in HLp2p2. exfalso. intuition congruence.
    }
    1-3: eauto 20 using mkRelated, execution_read_cons, combine_split_read_step.

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
         | H: state_machine.write_step _ _ _ _ _ |- _ =>
           rename H into WS; pose proof WS as WS';
           eapply state_machine.write_step_size_valid in WS';
           simpl in WS'; destruct WS' as [? | [? | [? | ?]]];
           try contradiction; try subst sz; try discriminate (* <- also gets rid of 8-byte MMIO case *)
         end.
    1-3: simp; erewrite write_step_isMMIOAddrB by eassumption.
    1-3: match goal with
         | E1: execution _ _, E2: execution _ _ |- _ =>
           pose proof (execution_unique _ _ _ E1 E2); subst; clear E2
         end.
    1-3: match goal with
         | |- context[device.runUntilResp ?p _ _] =>
           edestruct state_machine_write_to_device_write with (h2d := p)
             as (ignored & d' & s'' & RU & Rel' & WS');
             [eexists; match goal with
                       | H: state_machine.write_step ?n _ _ _ _ |- _ =>
                         change n at 1 with (2 ^ (Nat.log2 n))%nat in H
                       end; eassumption
             |eassumption
             |rewrite ? Z_word_N in * by lia; try reflexivity..]
         end.
    1-3: cbn -[HList.tuple Primitives.invalidateWrittenXAddrs];
      tlsimpl; simpl in RU; rewrite RU;
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
      eapply mkRelated.
      + eassumption.
      + match goal with
        | |- context[let '(_, _) := ?p in _] => destruct p eqn: E
        end.
        eapply nonMMIO_device_step_preserves_state_machine_state. 2: eassumption.
        1: instantiate (1 := tl_h2d_default); reflexivity.
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
      destruct One as (midL & midH & One & Rmid & Mid).
      specialize H1 with (1 := Mid) (2 := Rmid). specialize (H1 (S steps_done)).
      destruct H1 as (steps_remaining & finalL & finalH & Star & Rfinal & Pfinal).
      exists (S steps_remaining). simpl. rewrite One. eauto.
  Qed.

End WithParams.
