Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.Strings.String. Open Scope string_scope.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.ZnWords.
Require Import compiler.SeparationLogic.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraRiscvMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.DetIncrMachine.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitToRiscV.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitToRiscVProperties.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.Bedrock2ToCava.

Definition binary: list byte := Eval compute in Pipeline.instrencode put_wait_get_asm.

Axiom TODO: False.

Theorem IncrementWait_end2end_correct: forall p_functions p_call mH Rdata Rexec R (* <-? *)
          (initialL: ExtraRiscvMachine counter_device) input output_placeholder sched,
    -2^19 <= word.signed (word.sub p_functions p_call) < 2^19 ->
    128 <= word.unsigned (word.sub stack_pastend stack_start) ->
    word.unsigned (word.sub stack_pastend stack_start) mod 4 = 0 ->
    word.unsigned p_functions mod 4 = 0 ->
    word.unsigned p_call mod 4 = 0 ->
    initialL.(getLog) = [] ->
    machine_ok p_functions main_relative_pos stack_start stack_pastend binary p_call
               p_call mH Rdata Rexec initialL ->
    (scalar (word.of_Z input_ptr) input * scalar (word.of_Z output_ptr) output_placeholder * R)%sep mH ->
    exists steps_remaining finalL mH',
      run sched steps_remaining initialL = (Some tt, finalL) /\
      machine_ok p_functions main_relative_pos stack_start stack_pastend binary p_call
                 (word.add p_call (word.of_Z 4)) mH' Rdata Rexec finalL /\
      (scalar (word.of_Z input_ptr) input *
       scalar (word.of_Z output_ptr) (word.add (word.of_Z 1) input) * R)%sep mH' /\
      finalL.(getLog) = initialL.(getLog) (* no external interactions happened *).
Proof.
  intros.
  change binary with (Pipeline.instrencode put_wait_get_asm).
  refine (bedrock2_and_cava_system_correct
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    try eassumption.
  { apply sameset_ref. }
  { exact funcs_valid. }
  { apply List.dedup_NoDup_iff with (aeqb_spec:=String.eqb_spec). reflexivity. }
  { exact put_wait_get_compile_result_eq. }
  { (* check that the compiler emitted valid instructions: *)
    repeat (apply Forall_cons || apply Forall_nil).
    all: vm_compute; try intuition discriminate. }
  { unfold main_relative_pos.
    match goal with
    | H: _ <= ?x < _ |- _ <= _ + ?x' < _ => change x' with x
    end.
    Lia.lia. }
  { instantiate (2 := "main"). reflexivity. }
  { reflexivity. }
  { ZnWords. }
  { cbn. eexists. split; [reflexivity|].
    match goal with
    | |- _ _ ?x => replace x with device.reset_state by case TODO
    end.
    (* TODO put in machine_ok, but maybe require a "ready predicate" instead of reset state,
       and make sure that the IncrementWait program puts the device back into a ready state *)
    eapply MMIOToCava.initial_state_is_reset_state.
    reflexivity. }
  { refine (@WeakestPreconditionProperties.Proper_cmd _ StateMachineSemantics.ok _ _ _ _ _ _ _ _ _ _ _).
    1: eapply WeakestPreconditionProperties.Proper_call.
    2: {
      eapply main_correct. 1: eassumption.
      match goal with
      | H: ?t = ?t' |- _ ?t'' _ => replace t'' with t' by exact H
      end.
      reflexivity. }
    unfold post_main.
    repeat intro. Tactics.logical_simplify. Tactics.ssplit. 1: eassumption.
    eexists.
    eassumption.
  }
  Unshelve.
  all: unshelve eapply StateMachineSemantics.ok;
    exact IncrementWaitSemantics.state_machine_parameters_ok.
Qed.

(* Goal: bring this list down to only standard axioms like functional and propositional extensionality
Print Assumptions IncrementWait_end2end_correct.
*)
