(* based on Bedrock2Experiments.IncrementWait.IncrementWaitToRiscVProperties *)
Require Import Coq.derive.Derive.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.Pipeline.
Require Import Bedrock2Experiments.List.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitMMIO.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitProperties.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitToRiscV.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraRiscvMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.ExtraMMIORiscvMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.CavaIncrRiscvMachine.
Import Syntax.Coercions.
Local Open Scope string_scope.

Local Hint Resolve FlattenExpr.mk_Semantics_params_ok FlattenExpr_hyps : typeclass_instances.
Existing Instances constant_words spec_of_put_wait_get.

Instance consts_ok : constants_ok (constant_words (word_ok:=parameters.word_ok)).
Proof.
  constructor.
  { repeat constructor; cbv; intuition congruence. }
  { repeat constructor. }
  { repeat constructor. }
  { repeat constructor; cbv; intuition congruence. }
  { repeat constructor. }
Qed.

Instance Pipeline_assumptions : Pipeline.assumptions.
Proof.
  constructor.
  { apply MMIO.word_riscv_ok. }
  { exact MMIO.funname_env_ok. }
  { exact MMIO.locals_ok. }
  { exact PR. }
  { exact FlatToRiscv_hyps. }
  { exact ext_spec_ok. }
  { exact compile_ext_call_correct. }
  { reflexivity. }
Qed.

Definition post_main
           (input output_placeholder : parameters.word) R
           (t' : trace) (m' : Semantics.mem) : Prop :=
  (* trace is valid and leads to IDLE state *)
  execution t' IDLE
  /\ (scalar (word.of_Z input_ptr) input
     * scalar (word.of_Z output_ptr) (proc input)
     * R)%sep m'.

(* Location in the instructions that marks the start of the [main] routine *)
Definition main_relative_pos : Z. Admitted.
Definition compiled_instrs: list Decode.Instruction. Admitted.

Definition todo_replace: ExtraRiscvMachine device_state -> MetricRiscvMachine.
Admitted.

Definition runsTo:
  ExtraRiscvMachine device_state -> (ExtraRiscvMachine device_state -> Prop) -> Prop
  := runsToNonDet.runsTo system_step.

Lemma end2end
      input output_placeholder R Rdata Rexec
      (p_functions p_call : Utility.word)
      (mem : Pipeline.mem)
      (initial : ExtraRiscvMachine device_state) :
  (* given that the input and output pointers are valid and the input pointer
     points to input... *)
  (scalar (word.of_Z input_ptr) input
   * scalar (word.of_Z output_ptr) output_placeholder
   * R)%sep mem ->
  (* ...and the current machine state is OK... *)
  LowerPipeline.machine_ok
    p_functions main_relative_pos
    (stack_start ml) (stack_pastend ml)
    compiled_instrs p_call p_call mem Rdata Rexec (todo_replace initial) ->
  (* ...then, after the [main] routine is executed... *)
  runsTo initial
         (fun final =>
            exists mem',
              (* ...the postcondition of [main] holds on the new trace and
                 memory... *)
              post_main input output_placeholder R (getLog final) mem'
              (* ...and the new machine state is OK *)
              /\ LowerPipeline.machine_ok
                  p_functions main_relative_pos
                  (stack_start ml) (stack_pastend ml) compiled_instrs
                  p_call (word.add p_call (word.of_Z 4)) mem' Rdata Rexec
                  (todo_replace final)).
Proof.
Admitted.
