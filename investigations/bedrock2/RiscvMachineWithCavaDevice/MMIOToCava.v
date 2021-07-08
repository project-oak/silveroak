Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Datatypes.PropSet.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Platform.MetricSane.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.DetIncrMachine.
Require Import Bedrock2Experiments.StateMachineMMIOSpec.

Section WithParams.
  Context {word : Interface.word.word 32} {word_ok: word.ok word}
          {Registers: map.map Z word} {Registers_ok: map.ok Registers}
          {mem : Interface.map.map word Byte.byte} {mem_ok: map.ok mem}
          {state_machine_params: StateMachineSemantics.parameters.parameters 32 word mem}
          {state_machine_params_ok: StateMachineSemantics.parameters.ok state_machine_params}
          {D: device}
          (device_state_related: StateMachineSemantics.parameters.state -> D -> Prop).

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
    (*
      above the line:
      Run.run1 with Bedrock2Experiments.Riscv.MetricMinimalMMIO.IsRiscvMachine
      below the line:
      Run.run1 with Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.IsRiscvMachine

      would like to say "forall monadic programs, L behaves like H" --> L needs to go through
      monad materialization as well *)

    (* not sure if useful: *)
    pose proof (run1_sane Decode.RV32I) as A.
    unfold MetricPrimitives.mcomp_sane, Primitives.mcomp_sat, Primitives.valid_machine,
        MetricMinimalMMIO.MetricMinimalMMIOPrimitivesParams, MinimalMMIO.isMMIOAddr,
        StateMachineMMIOSpec in A.
    specialize A with (2 := H0). cbv beta in A.
    inversion H. subst. clear H.
    destruct A as (A & _). 1: split; assumption.
    destruct A as (_ & finalH & Pf & Un & Dj).

  Admitted.

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
