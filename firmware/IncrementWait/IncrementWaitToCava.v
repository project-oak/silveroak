Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.Strings.String. Open Scope string_scope.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.ZnWords.
Require Import compiler.SeparationLogic.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraRiscvMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.CavaIncrementDevice.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitToRiscV.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitToRiscVProperties.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.Bedrock2ToCava.

Definition binary: list byte := Eval compute in Pipeline.instrencode put_wait_get_asm.

Theorem IncrementWait_end2end_correct: forall p_functions ret_addr mH (Rdata Rexec R: mem -> Prop)
          (initialL: ExtraRiscvMachine counter_device) input sched,
    word.unsigned (word.sub stack_pastend stack_start) mod 4 = 0 ->
    word.unsigned p_functions mod 4 = 0 ->
    word.unsigned ret_addr mod 4 = 0 ->
    machine_ok p_functions stack_start stack_pastend binary mH Rdata Rexec initialL ->
    R mH ->
    map.get initialL.(getRegs) RegisterNames.a0 = Some input ->
    map.get initialL.(getRegs) RegisterNames.ra = Some ret_addr ->
    word.unsigned ret_addr mod 4 = 0 ->
    initialL.(getLog) = [] ->
    initialL.(getPc) = word.add p_functions (word.of_Z put_wait_get_relative_pos) ->
    exists steps_remaining finalL mH',
      run sched steps_remaining initialL = (Some tt, finalL) /\
      machine_ok p_functions stack_start stack_pastend binary mH' Rdata Rexec finalL /\
      R mH' /\
      map.get finalL.(getRegs) RegisterNames.a0 = Some (word.add (word.of_Z 1) input) /\
      finalL.(getPc) = ret_addr /\
      finalL.(getLog) = initialL.(getLog) (* no external interactions happened *).
Proof.
  intros.
  change binary with (Pipeline.instrencode put_wait_get_asm).
  edestruct bedrock2_and_cava_system_correct with
      (f_entry_name := "put_wait_get")
      (stack_start := stack_start) (stack_pastend := stack_pastend)
      (postH := fun m' retvals =>  R m' /\ retvals = [word.add (word.of_Z 1) input])
    as (steps_remaining & finalL & mH' & retvals & Rn & GM & A & Eq & M & HP & HL);
    lazymatch goal with
    | |- _ mod _ = _ => idtac
    | |- _ => try eassumption
    end.
  { exact funcs_valid. }
  { apply List.dedup_NoDup_iff. reflexivity. }
  { exact put_wait_get_compile_result_eq. }
  { (* check that the compiler emitted valid instructions: *)
    repeat (apply Forall_cons || apply Forall_nil).
    all: vm_compute; try intuition discriminate. }
  { reflexivity. }
  { vm_compute. discriminate. }
  { assumption. }
  { assumption. }
  { assumption. }
  { eapply WeakestPreconditionProperties.Proper_call.
    2: eapply IncrementWaitProperties.put_wait_get_correct.
    2: eassumption.
    2: reflexivity.
    unfold Morphisms.pointwise_relation, Basics.impl.
    intros. fwd.
    unfold IncrementWaitSemantics.proc.
    split. 1: split; [assumption|reflexivity].
    eexists; split; [eassumption|reflexivity]. }
  { cbn -[map.get].
    match goal with
    | H: map.get _ RegisterNames.a0 = Some input |-
      match ?x with _ => _ end = _ => replace x with (Some input)
    end.
    reflexivity. }
  { eassumption. }
  { cbn -[map.get] in GM. fwd. eauto 10. }
Qed.

(* Goal: bring this list down to only standard axioms like functional and propositional extensionality
Print Assumptions IncrementWait_end2end_correct.
*)
