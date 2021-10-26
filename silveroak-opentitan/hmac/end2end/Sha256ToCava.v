Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.Strings.String. Open Scope string_scope.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.ZnWords.
Require Import compiler.SeparationLogic.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraRiscvMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import HmacEnd2End.CavaHmacDevice.
Require Import HmacSoftware.Sha256ToRiscV.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.Bedrock2ToCava.

Definition binary: list byte := Eval compute in Pipeline.instrencode sha256_asm.

(* TODO replace axiom from HmacSemantics with actual spec *)
Definition sha256 := HmacSemantics.sha256.

Axiom TODO: False.

Theorem sha256_example_end2end_correct: forall p_functions p_call mH Rdata Rexec R (* <-? *)
          (initialL: ExtraRiscvMachine hmac_device) digest_addr input_addr input_len
          input output_placeholder sched,
    -2^19 <= word.signed (word.sub p_functions p_call) < 2^19 ->
    128 <= word.unsigned (word.sub stack_pastend stack_start) ->
    word.unsigned (word.sub stack_pastend stack_start) mod 4 = 0 ->
    word.unsigned p_functions mod 4 = 0 ->
    word.unsigned p_call mod 4 = 0 ->
    initialL.(getLog) = [] ->
    machine_ok p_functions stack_start stack_pastend binary
               mH Rdata Rexec initialL ->
    Z.of_nat (length input) = word.unsigned input_len ->
    Z.of_nat (length output_placeholder) = 32 ->
    input_addr <> word.of_Z 0 ->
    digest_addr <> word.of_Z 0 ->
    (bytearray input_addr input * bytearray digest_addr output_placeholder * R)%sep mH ->
    exists steps_remaining finalL mH',
      run sched steps_remaining initialL = (Some tt, finalL) /\
      machine_ok p_functions stack_start stack_pastend binary
                 mH' Rdata Rexec finalL /\
    (bytearray input_addr input * bytearray digest_addr (sha256 input) * R)%sep mH' /\
      finalL.(getLog) = initialL.(getLog) (* no external interactions happened *).
Proof.
  intros.
  change binary with (Pipeline.instrencode sha256_asm).
Abort.
(*
  refine (bedrock2_and_cava_system_correct
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    try eassumption.
  { exact funcs_valid. }
  { apply List.dedup_NoDup_iff with (aeqb_spec:=String.eqb_spec). reflexivity. }
  { exact sha256_compile_result_eq. }
  { (* check that the compiler emitted valid instructions: *)
    repeat (apply Forall_cons || apply Forall_nil).
    all: try (vm_compute; intuition discriminate). }
  { let p := eval cbv in main_relative_pos in change main_relative_pos with p. Lia.lia. }
  { instantiate (2 := "main"). reflexivity. }
  { reflexivity. }
  { vm_compute. discriminate. }
  { refine (WeakestPreconditionProperties.Proper_cmd _ _ _ _ _ _ _ _ _ _ _).
    1: eapply WeakestPreconditionProperties.Proper_call.
    2: {
      eapply main_correct with (idlebuffer := List.repeat Byte.x00 32); cycle -2; try eassumption.
      match goal with
      | H: ?t = ?t' |- _ ?t'' _ => replace t'' with t' by exact H
      end.
      cbn.
      case TODO.
      (* make length of digest buffer match, and how to make it unique to satisfy Cava connection? *)
    }
    unfold Sha256ExampleProperties.sha256_post.
    repeat intro. Tactics.logical_simplify. Tactics.ssplit.
    { unfold sha256. ecancel_assumption. }
    eexists. split; [eassumption|]. cbn. case TODO.
    (* here, IDLE state with a sha in its digest_buffer must be an initial state *)
  }
  Unshelve. case TODO. (* initial state will be determined *)
Qed.
*)

(* Goal: bring this list down to only standard axioms like functional and propositional extensionality
Print Assumptions sha256_example_end2end_correct.
 *)
