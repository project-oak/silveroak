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
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineMMIO.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitProperties.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitToRiscV.
Import Syntax.Coercions.
Local Open Scope string_scope.

Definition post_main
           (input output_placeholder : word) R
           (t' : trace) (m' : mem) : Prop :=
  (* trace is valid and leads to IDLE state *)
  execution t' IDLE
  /\ (scalar (word.of_Z input_ptr) input
     * scalar (word.of_Z output_ptr) (proc input)
     * R)%sep m'.

Lemma main_correct
      fs input output_placeholder
      R (t : trace) m l :
  (scalar (word.of_Z input_ptr) input
   * scalar (word.of_Z output_ptr) output_placeholder
   * R)%sep m ->
  execution t IDLE ->
  WeakestPrecondition.cmd
    (WeakestPrecondition.call (put_wait_get :: fs))
    main_body t m l
    (fun t' m' _ => post_main input output_placeholder R t' m').
Proof.
  intros.
  repeat straightline.
  pose proof (put_wait_get_correct fs).
  straightline_call; [ eassumption .. | ].
  repeat straightline_with_map_lookup.
  eexists; split; repeat straightline_with_map_lookup; [ ].
  split; [ assumption | ].
  ecancel_assumption.
Qed.

Lemma exec_put_wait_get fs input output_placeholder R
      (t : trace) (m : mem) (l : ProgramSemantics32.locals) mc :
  (scalar (word.of_Z input_ptr) input
   * scalar (word.of_Z output_ptr) output_placeholder
   * R)%sep m ->
  execution t IDLE ->
  NoDup (map fst (main :: put_wait_get :: fs)) ->
  exec (map.of_list (main :: put_wait_get :: fs))
       main_body t m l mc
       (fun t' m' _ _ => post_main input output_placeholder R t' m').
Proof.
  intros. apply sound_cmd; [ assumption | ].
  eapply main_correct. (* relying on conversion to prepend `main` to list of functions *)
  all: eauto.
Qed.

(* Location in the instructions that marks the start of the [main] routine *)
Definition main_relative_pos : Z.
  let x := constr:(map.get
                     (snd (fst put_wait_get_compile_result))
                     main) in
  let x := eval vm_compute in x in
      lazymatch x with
      | Some ?y => exact y
      end.
Defined.

Definition stack_start: word := word.of_Z (8*2^10).
Definition stack_pastend: word := word.of_Z (16*2^10).

Lemma funcs_valid: ExprImp.valid_funs (map.of_list funcs).
Proof.
  cbv [funcs map.of_list ExprImp.valid_funs main put_wait_get]. intros *.
  rewrite !map.get_put_dec, map.get_empty.
  repeat destruct_one_match; inversion 1; cbv [ExprImp.valid_fun].
  all:ssplit.
  all:apply dedup_NoDup_iff with (aeqb_spec:=String.eqb_spec).
  all:reflexivity.
Qed.

Lemma put_wait_get_asm_correct
      input output_placeholder R Rdata Rexec
      (p_functions p_call : word)
      (mem : mem)
      (initial : MetricRiscvMachine) :
  (* given that the input and output pointers are valid and the input pointer
     points to input... *)
  (scalar (word.of_Z input_ptr) input
   * scalar (word.of_Z output_ptr) output_placeholder
   * R)%sep mem ->
  (* ...and the trace so far leads to an IDLE state... *)
  execution (getLog initial) IDLE ->
  (* ...and the current machine state is OK... *)
  let instrs := fst (fst (put_wait_get_compile_result)) in
  LowerPipeline.machine_ok
    p_functions main_relative_pos
    stack_start stack_pastend
    instrs p_call p_call mem Rdata Rexec initial ->
  (* ...then, after the [main] routine is executed... *)
  runsTo initial
         (fun final : MetricRiscvMachine =>
            exists mem',
              (* ...the postcondition of [main] holds on the new trace and
                 memory... *)
              post_main input output_placeholder R (getLog final) mem'
              (* ...and the new machine state is OK *)
              /\ LowerPipeline.machine_ok
                  p_functions main_relative_pos
                  stack_start stack_pastend
                  instrs p_call (word.add p_call (word.of_Z 4)) mem' Rdata Rexec final).
Proof.
  intros.
  pose proof compiler_correct as P.
  specialize P with (functions := map.of_list funcs).
  specialize P with (mc:=bedrock2.MetricLogging.EmptyMetricLog).
  specialize P with (f_entry_name := main)
         (postH:=post_main input output_placeholder R).
  match type of P with
  | context[?fs] => lazymatch fs with
                    | (map.of_list funcs) =>
                      let fs' := eval cbv [map.of_list put_wait_get main funcs] in fs in
                          change fs with fs' in P
                   end
  end.
  eapply P.
  { eapply compile_ext_call_correct. }
  { intros. reflexivity. }
  { exact funcs_valid. }
  { apply put_wait_get_compile_result_eq. }
  { rewrite !map.get_put_dec, map.get_empty.
    rewrite String.eqb_refl. reflexivity. }
  { reflexivity. }
  { vm_compute. congruence. }
  { reflexivity. }
  { apply exec_put_wait_get with (fs:=[]); eauto.
    apply dedup_NoDup_iff with (aeqb_spec:=String.eqb_spec).
    reflexivity. }
  { eauto. }
Qed.
