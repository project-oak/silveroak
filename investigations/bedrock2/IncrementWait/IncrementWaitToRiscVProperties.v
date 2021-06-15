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
Import Syntax.Coercions.
Local Open Scope string_scope.

Local Hint Resolve FlattenExpr.mk_Semantics_params_ok FlattenExpr_hyps : typeclass_instances.
Existing Instances constant_words spec_of_put_wait_get.

Instance consts_ok : constants_ok (constant_words (word_ok:=parameters.word_ok)).
Proof.
  constructor.
  { eapply dedup_NoDup_iff. reflexivity. }
  { repeat constructor. }
  { repeat constructor. }
  { eapply dedup_NoDup_iff. reflexivity. }
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

Local Ltac simplify_implicits :=
  change semantics_parameters
  with (FlattenExpr.mk_Semantics_params
          Pipeline.FlattenExpr_parameters) in *.

Lemma main_correct
      fs input output_placeholder
      R (t : @trace semantics_parameters) m l :
  (scalar (word.of_Z input_ptr) input
   * scalar (word.of_Z output_ptr) output_placeholder
   * R)%sep m ->
  execution t IDLE ->
  WeakestPrecondition.cmd
    (WeakestPrecondition.call (put_wait_get :: fs))
    main_body t m l
    (fun t' m' _ => post_main input output_placeholder R t' m').
Proof.
  intros. simplify_implicits.
  repeat straightline.
  pose proof (put_wait_get_correct
                (consts:=constant_words (word_ok:=parameters.word_ok)) fs).
  straightline_call; [ eassumption .. | ].
  repeat straightline_with_map_lookup.
  eexists; split; repeat straightline_with_map_lookup; [ ].
  split; [ assumption | ].

  (* change the implicit arguments of scalar to match hypothesis *)
  lazymatch goal with
  | H : sep _ _ ?m |- sep _ _ ?m =>
    lazymatch type of H with
    | context [(@scalar ?a1 ?b1 ?c1)] =>
      lazymatch goal with
      | |- context [(@scalar ?a2 ?b2 ?c2)] =>
        change a2 with a1; change b2 with b1; change c2 with c1
      end
    end
  end.
  ecancel_assumption.
Qed.

Lemma exec_put_wait_get fs input output_placeholder R
      (t : trace) (m : Semantics.mem) (l : Semantics.locals) mc :
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
  apply main_correct; eauto.
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

Lemma put_wait_get_asm_correct
      input output_placeholder R Rdata Rexec
      (p_functions p_call : Utility.word)
      (mem : Pipeline.mem)
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
    (stack_start ml) (stack_pastend ml)
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
                  (stack_start ml) (stack_pastend ml)
                  instrs p_call (word.add p_call (word.of_Z 4)) mem' Rdata Rexec final).
Proof.
  intros.
  let fs := constr:(map.of_list funcs) in
  let fs := eval cbv [map.of_list put_wait_get main funcs] in fs in
  eapply compiler_correct
    with (functions:=fs)
         (mc:=bedrock2.MetricLogging.EmptyMetricLog)
         (f_entry_name := main)
         (postH:=post_main input output_placeholder R).
  { constructor; vm_compute; congruence. }
  { cbv [ExprImp.valid_funs]. intros *.
    rewrite !map.get_put_dec, map.get_empty.
    repeat destruct_one_match; inversion 1; cbv [ExprImp.valid_fun].
    all:ssplit.
    all:apply dedup_NoDup_iff with (aeqb_spec:=String.eqb_spec).
    all:reflexivity. }
  { apply put_wait_get_compile_result_eq. }
  { rewrite !map.get_put_dec, map.get_empty.
    rewrite String.eqb_refl. reflexivity. }
  { reflexivity. }
  { vm_compute. congruence. }
  { apply exec_put_wait_get with (fs:=[]); eauto.
    apply dedup_NoDup_iff with (aeqb_spec:=String.eqb_spec).
    reflexivity. }
  { eauto. }
Qed.
