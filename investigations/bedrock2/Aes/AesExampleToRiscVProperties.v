Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Array.
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
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.List.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.StateMachineMMIO.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.LibBase.AbsMMIOProperties.
Require Import Bedrock2Experiments.Aes.Constants.
Require Import Bedrock2Experiments.Aes.AesExample.
Require Import Bedrock2Experiments.Aes.AesExampleProperties.
Require Import Bedrock2Experiments.Aes.AesProperties.
Require Import Bedrock2Experiments.Aes.AesSemantics.
Require Import Bedrock2Experiments.Aes.AesToRiscV.
Require Import Bedrock2Experiments.Aes.AesExampleToRiscV.
Import Syntax.Coercions.
Import ListNotations.
Local Open Scope string_scope.

Local Hint Resolve FlattenExpr.mk_Semantics_params_ok FlattenExpr_hyps : typeclass_instances.
Existing Instances constant_literals spec_of_aes_encrypt.

(* add a stronger hint for state_machine_parameters and state_machine_parameters_ok *)
Local Hint Extern 1 (StateMachineSemantics.parameters _ _ _) =>
exact state_machine_parameters : typeclass_instances.
Local Hint Extern 1 (StateMachineSemantics.parameters.ok _) =>
exact state_machine_parameters_ok : typeclass_instances.

Instance consts_ok : aes_constants_ok consts.
Proof.
  apply Build_aes_constants_ok with (mode_size:=3) (key_len_size:=3).
  { eapply dedup_NoDup_iff. reflexivity. }
  { repeat constructor. }
  { repeat constructor.
    all:vm_compute; congruence. }
  { eapply dedup_NoDup_iff. reflexivity. }
  { repeat constructor. all: vm_compute. all: congruence. }
  { reflexivity. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { vm_compute; ssplit; congruence. }
  { repeat constructor;
    vm_compute; ssplit; intuition congruence. }
  { repeat constructor;
    vm_compute; ssplit; intuition congruence. }
  { repeat constructor;
    vm_compute; ssplit; intuition congruence. }
Qed.

Instance Pipeline_assumptions : Pipeline.assumptions.
Proof.
  constructor.
  { apply MMIO.word_riscv_ok. }
  { exact MMIO.funname_env_ok. }
  { exact MMIO.locals_ok. }
  { exact PR. }
  { exact FlatToRiscv_hyps. }
  { pose proof state_machine_parameters_ok.
    (* TODO why does
    Existing Instance state_machine_parameters_ok.
    not work? *)
    exact (ext_spec_ok (p := @state_machine_parameters aes_parameters consts aes_timing)). }
  { exact (compile_ext_call_correct (state_machine_parameters_ok:=state_machine_parameters_ok)). }
  { reflexivity. }
Qed.

Definition post_main
           (in0 in1 in2 in3 iv0 iv1 iv2 iv3
                key0 key1 key2 key3 key4 key5 key6 key7
            : parameters.word) R
           (t' : trace) (m' : Semantics.mem) : Prop :=
  let '(out0,out1,out2,out3) :=
      parameters.aes_spec
        false (key0, key1, key2, key3, key4, key5, key6, key7)
        (iv0, iv1, iv2, iv3) (in0, in1, in2, in3) in
  (* trace is valid and leads to IDLE state *)
  (exists data, execution t' (IDLE data))
  (* input is unchanged and output holds the result of AES encrypt *)
  /\ (array scalar32 (word.of_Z 4) (word.of_Z input_data_ptr) [in0;in1;in2;in3]
     * array scalar32 (word.of_Z 4) (word.of_Z input_key_ptr)
             [key0;key1;key2;key3;key4;key5;key6;key7]
     * array scalar32 (word.of_Z 4) (word.of_Z input_iv_ptr) [iv0;iv1;iv2;iv3]
     * array scalar32 (word.of_Z 4) (word.of_Z output_ptr) [out0;out1;out2;out3]
     * R)%sep m'.

Local Ltac simplify_implicits :=
  change (FlattenExpr.mk_Semantics_params
          Pipeline.FlattenExpr_parameters) with semantics_parameters in *;
  change Semantics.width with 32 in *;
  change Semantics.word with parameters.word in *.

Lemma main_correct
      fs in0 in1 in2 in3 iv0 iv1 iv2 iv3
      key0 key1 key2 key3 key4 key5 key6 key7
      output_placeholder
      R (t : @trace semantics_parameters) m l :
  (array scalar32 (word.of_Z 4) (word.of_Z input_data_ptr) [in0;in1;in2;in3]
   * array scalar32 (word.of_Z 4) (word.of_Z input_key_ptr)
           [key0;key1;key2;key3;key4;key5;key6;key7]
   * array scalar32 (word.of_Z 4) (word.of_Z input_iv_ptr) [iv0;iv1;iv2;iv3]
   * array scalar32 (word.of_Z 4) (word.of_Z output_ptr) output_placeholder
   * R)%sep m ->
  length output_placeholder = 4%nat ->
  spec_of_aes_encrypt fs ->
  execution (p:=state_machine_parameters) t UNINITIALIZED ->
  WeakestPrecondition.cmd
    (WeakestPrecondition.call fs)
    main_body t m l
    (fun t' m' _ =>
       post_main in0 in1 in2 in3 iv0 iv1 iv2 iv3
                 key0 key1 key2 key3 key4 key5 key6 key7
                 R t' m').
Proof.
  intros. repeat straightline.
  straightline_call. 1,2,3: eassumption.
  (* `ecancel_assumption` gets severely stuck in PARAMRECORDS problems, but
     fortunately `eassumption` just works. *)
  cbv [post_main]. simplify_implicits.
  repeat destruct_one_match_hyp.
  repeat straightline.
  ssplit; [ solve [eauto] | ].
  (* TODO fix PARAMRECORDS issues so that ecancel_assumption works again *)
  use_sep_assumption.
  cancel.
  cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
  cancel_seps_at_indices 0%nat 1%nat; [reflexivity|].
  cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
  cancel_seps_at_indices 0%nat 0%nat; [reflexivity|].
  reflexivity.
  Unshelve.
  all: pose proof state_machine_parameters_ok; exact ok.
Qed.

Lemma exec_main
      fs in0 in1 in2 in3 iv0 iv1 iv2 iv3
      key0 key1 key2 key3 key4 key5 key6 key7
      output_placeholder R
      (t : trace) (m : Semantics.mem) (l : Semantics.locals) mc :
  (array scalar32 (word.of_Z 4) (word.of_Z input_data_ptr) [in0;in1;in2;in3]
   * array scalar32 (word.of_Z 4) (word.of_Z input_key_ptr)
           [key0;key1;key2;key3;key4;key5;key6;key7]
   * array scalar32 (word.of_Z 4) (word.of_Z input_iv_ptr) [iv0;iv1;iv2;iv3]
   * array scalar32 (word.of_Z 4) (word.of_Z output_ptr) output_placeholder
   * R)%sep m ->
  length output_placeholder = 4%nat ->
  spec_of_aes_encrypt (main :: fs) ->
  execution t UNINITIALIZED ->
  NoDup (map fst (main :: fs)) ->
  exec (map.of_list (main :: fs))
       main_body t m l mc
       (fun t' m' _ _=>
          post_main in0 in1 in2 in3 iv0 iv1 iv2 iv3
                    key0 key1 key2 key3 key4 key5 key6 key7
                    R t' m').
Proof.
  intros. apply sound_cmd; [ assumption | ].
  eapply main_correct; eauto.
Qed.

(* Location in the instructions that marks the start of the [main] routine *)
Definition main_relative_pos : Z.
  let x := constr:(map.get
                     (snd (fst aes_example_compile_result))
                     main) in
  let x := eval vm_compute in x in
      lazymatch x with
      | Some ?y => exact y
      end.
Defined.

Lemma aes_example_asm_correct
      in0 in1 in2 in3 iv0 iv1 iv2 iv3
      key0 key1 key2 key3 key4 key5 key6 key7
      output_placeholder R Rdata Rexec
      (p_functions p_call : Utility.word)
      (mem : Pipeline.mem)
      (initial : MetricRiscvMachine) :
  (* given that the input and output pointers are valid and the input pointers
     point to the in, key, and iv values... *)
  (array scalar32 (word.of_Z 4) (word.of_Z input_data_ptr) [in0;in1;in2;in3]
   * array scalar32 (word.of_Z 4) (word.of_Z input_key_ptr)
           [key0;key1;key2;key3;key4;key5;key6;key7]
   * array scalar32 (word.of_Z 4) (word.of_Z input_iv_ptr) [iv0;iv1;iv2;iv3]
   * array scalar32 (word.of_Z 4) (word.of_Z output_ptr) output_placeholder
   * R)%sep mem ->
  (* ...and there is enough space for the output *)
  length output_placeholder = 4%nat ->
  (* ...and the trace so far leads to an UNINITIALIZED state... *)
  execution (getLog initial) UNINITIALIZED ->
  (* ...and the current machine state is OK... *)
  let instrs := fst (fst (aes_example_compile_result)) in
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
              post_main in0 in1 in2 in3 iv0 iv1 iv2 iv3
                        key0 key1 key2 key3 key4 key5 key6 key7
                        R (getLog final) mem'
              (* ...and the new machine state is OK *)
              /\ LowerPipeline.machine_ok
                  p_functions main_relative_pos
                  (stack_start ml) (stack_pastend ml)
                  instrs p_call (word.add p_call (word.of_Z 4)) mem' Rdata Rexec final).
Proof.
  intros.
  let fs := constr:(map.of_list (funcs ++ AesToRiscV.funcs)) in
  eapply compiler_correct
    with (functions:=fs)
         (mc:=bedrock2.MetricLogging.EmptyMetricLog)
         (f_entry_name := main)
         (postH:=post_main
                   in0 in1 in2 in3 iv0 iv1 iv2 iv3
                   key0 key1 key2 key3 key4 key5 key6 key7 R).
  { constructor; vm_compute; congruence. }
  { cbv [ExprImp.valid_funs]. intros *.
    cbv [map.of_list
           List.app
           AbsMMIO.abs_mmio_read32
           aes_encrypt main
           Aes.aes_init Aes.aes_key_put
           Aes.aes_iv_put Aes.aes_data_put
           Aes.aes_data_get Aes.aes_data_ready
           Aes.aes_data_valid Aes.aes_idle
           Aes.aes_data_put_wait Aes.aes_data_get_wait
           funcs AesToRiscV.funcs].
    rewrite !map.get_put_dec, map.get_empty.
    repeat destruct_one_match; inversion 1; cbv [ExprImp.valid_fun].
    all:ssplit.
    all:apply dedup_NoDup_iff with (aeqb_spec:=String.eqb_spec).
    all:reflexivity. }
  { exact aes_example_compile_result_eq. }
  { cbv [map.of_list
           List.app
           AbsMMIO.abs_mmio_read32
           aes_encrypt main
           Aes.aes_init Aes.aes_key_put
           Aes.aes_iv_put Aes.aes_data_put
           Aes.aes_data_get Aes.aes_data_ready
           Aes.aes_data_valid Aes.aes_idle
           Aes.aes_data_put_wait Aes.aes_data_get_wait
           funcs AesToRiscV.funcs].
    rewrite !map.get_put_dec, map.get_empty.
    rewrite String.eqb_refl. reflexivity. }
  { reflexivity. }
  { vm_compute. congruence. }
  { eapply exec_main; eauto.
    { apply aes_encrypt_correct.
      {
        apply aes_init_correct. }
      { apply aes_key_put_correct. }
      { apply aes_iv_put_correct. }
      { apply aes_data_put_wait_correct.
        { apply aes_data_ready_correct.
          apply abs_mmio_read32_correct. }
        { apply aes_data_put_correct. } }
      { apply aes_data_get_wait_correct.
        { apply aes_data_valid_correct.
          apply abs_mmio_read32_correct. }
        { apply aes_data_get_correct. } } }
    { apply dedup_NoDup_iff with (aeqb_spec:=String.eqb_spec).
      reflexivity. } }
  { eauto. }
Qed.
