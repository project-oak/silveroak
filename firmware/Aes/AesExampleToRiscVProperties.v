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

Definition post_main
           (in0 in1 in2 in3 iv0 iv1 iv2 iv3
                key0 key1 key2 key3 key4 key5 key6 key7
            : word) R
           (t' : trace) (m' : mem) : Prop :=
  let '(out0,out1,out2,out3) :=
      aes_spec
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

Lemma main_correct
      fs in0 in1 in2 in3 iv0 iv1 iv2 iv3
      key0 key1 key2 key3 key4 key5 key6 key7
      output_placeholder
      R (t : trace) m l :
  (array scalar32 (word.of_Z 4) (word.of_Z input_data_ptr) [in0;in1;in2;in3]
   * array scalar32 (word.of_Z 4) (word.of_Z input_key_ptr)
           [key0;key1;key2;key3;key4;key5;key6;key7]
   * array scalar32 (word.of_Z 4) (word.of_Z input_iv_ptr) [iv0;iv1;iv2;iv3]
   * array scalar32 (word.of_Z 4) (word.of_Z output_ptr) output_placeholder
   * R)%sep m ->
  length output_placeholder = 4%nat ->
  spec_of_aes_encrypt fs ->
  execution t UNINITIALIZED ->
  WeakestPrecondition.cmd
    (WeakestPrecondition.call fs)
    main_body t m l
    (fun t' m' _ =>
       post_main in0 in1 in2 in3 iv0 iv1 iv2 iv3
                 key0 key1 key2 key3 key4 key5 key6 key7
                 R t' m').
Proof.
  intros. repeat straightline.
  straightline_call. 1: ecancel_assumption. 1,2: eassumption.
  cbv [post_main].
  repeat destruct_one_match_hyp.
  repeat straightline.
  ssplit; [ solve [eauto] | ecancel_assumption ].
Qed.

Lemma exec_main
      fs in0 in1 in2 in3 iv0 iv1 iv2 iv3
      key0 key1 key2 key3 key4 key5 key6 key7
      output_placeholder R
      (t : trace) (m : mem) l mc :
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
      | Some (_, _, ?y) => exact y
      end.
Defined.

Lemma aes_example_asm_correct
      in0 in1 in2 in3 iv0 iv1 iv2 iv3
      key0 key1 key2 key3 key4 key5 key6 key7
      output_placeholder R Rdata Rexec
      (p_functions ret_addr : word)
      (mem : mem)
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
  LowerPipeline.machine_ok p_functions (stack_start ml) (stack_pastend ml)
                           instrs mem Rdata Rexec initial ->
  (* ...and the pc points to the first instruction of main... *)
  initial.(getPc) = word.add p_functions (word.of_Z main_relative_pos) ->
  (* ...and the return address register contains a valid ret_addr... *)
  map.get initial.(getRegs) RegisterNames.ra = Some ret_addr ->
  word.unsigned ret_addr mod 4 = 0 ->
  (* ...then, after the [main] routine is executed... *)
  runsTo initial
         (fun final : MetricRiscvMachine =>
            exists mem',
              (* ...the postcondition of [main] holds on the new trace and
                 memory... *)
              post_main in0 in1 in2 in3 iv0 iv1 iv2 iv3
                        key0 key1 key2 key3 key4 key5 key6 key7
                        R (getLog final) mem'
              (* ...and the new machine state is OK... *)
              /\ LowerPipeline.machine_ok p_functions (stack_start ml) (stack_pastend ml)
                   instrs mem' Rdata Rexec final
              (* ...and program execution will continue at ret_addr *)
              /\ final.(getPc) = ret_addr).
Proof.
  intros.
  pose proof aes_example_compile_result_eq as CR.
  destruct aes_example_compile_result as ((insts & finfo) & req_stack_size) eqn: CE.
  let fs := constr:(map.of_list (funcs ++ AesToRiscV.funcs)) in
  pose proof compiler_correct as P;
  specialize P with (functions := fs)
                    (fname := main)
                    (post := fun t m retvals => post_main
                       in0 in1 in2 in3 iv0 iv1 iv2 iv3
                       key0 key1 key2 key3 key4 key5 key6 key7 R t m).
  edestruct P as (main_rel_pos & G & Q); clear P.
  { exact compile_ext_call_correct. }
  { intros. reflexivity. }
  { cbv [ExprImp.valid_funs]. intros *.
    cbv [map.of_list
           List.app
           AbsMMIO.abs_mmio_read32
           AbsMMIO.abs_mmio_write32
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
    all:apply dedup_NoDup_iff.
    all:reflexivity. }
  { exact CR. }
  { cbv [map.of_list
           List.app
           AbsMMIO.abs_mmio_read32
           AbsMMIO.abs_mmio_write32
           aes_encrypt main
           Aes.aes_init Aes.aes_key_put
           Aes.aes_iv_put Aes.aes_data_put
           Aes.aes_data_get Aes.aes_data_ready
           Aes.aes_data_valid Aes.aes_idle
           Aes.aes_data_put_wait Aes.aes_data_get_wait
           funcs AesToRiscV.funcs].
    rewrite !map.get_put_dec, map.get_empty.
    rewrite String.eqb_refl. reflexivity. }
  { intros.
    eapply ExprImp.weaken_exec. {
      eapply exec_main; eauto.
      { apply aes_encrypt_correct. {
          apply aes_init_correct.
          apply abs_mmio_write32_correct.
        }
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
      { apply dedup_NoDup_iff. reflexivity. } }
    { cbv beta. intros. exists nil. split. 1: reflexivity. assumption. } }
  eapply runsToNonDet.runsTo_weaken. 1: eapply Q. all: clear Q.
  all: try match goal with
           | H: context[LowerPipeline.machine_ok] |- context[LowerPipeline.machine_ok] => exact H
           end.
  all: try eassumption.
  { apply (f_equal snd) in CE. cbn [snd] in CE. subst req_stack_size. vm_compute. congruence. }
  { reflexivity. }
  { apply (f_equal fst) in CE. apply (f_equal snd) in CE. cbn [fst snd] in CE. subst finfo.
    vm_compute in G. inversion G. subst main_rel_pos.
    assumption. }
  { vm_compute. reflexivity. }
  { reflexivity. }
  { cbv beta. intros. logical_simplify. subst. eauto. }
Qed.
