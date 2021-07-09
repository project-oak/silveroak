Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Simp.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricSane.
Require Import compiler.SeparationLogic.
Require Import compiler.Pipeline.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.DetIncrMachine.
Require Import Bedrock2Experiments.StateMachineMMIOSpec.
Require Import Bedrock2Experiments.StateMachineMMIO.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Section WithParams.
  Context {word : Interface.word.word 32} {word_ok: word.ok word}
          {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}
          {Registers: map.map Z word} {Registers_ok: map.ok Registers}
          {mem : Interface.map.map word Byte.byte} {mem_ok: map.ok mem}
          {state_machine_params: StateMachineSemantics.parameters.parameters 32 word mem}
          {state_machine_params_ok: StateMachineSemantics.parameters.ok state_machine_params}
          {D: device}
          (device_state_related: StateMachineSemantics.parameters.state -> D -> Prop)
          (sched: schedule).

  Open Scope ilist_scope.

  Global Instance MMIO_compiler_params: StateMachineMMIO.MMIO.parameters := {|
    MMIO.word := word;
    MMIO.word_ok := _;
    MMIO.word_riscv_ok := _;
    MMIO.mem := mem;
    MMIO.mem_ok := mem_ok;
    MMIO.locals := Registers;
    MMIO.locals_ok := Registers_ok;
    MMIO.funname_env := SortedListString.map;
    MMIO.funname_env_ok := SortedListString.ok;
  |}.

  Global Instance pipeline_params: Pipeline.parameters := {|
    Pipeline.W := _;
    Pipeline.mem := mem;
    Pipeline.Registers := Registers;
    Pipeline.string_keyed_map := _;
    Pipeline.ext_spec := StateMachineSemantics.ext_spec;
    Pipeline.compile_ext_call :=
      @FlatToRiscvDef.FlatToRiscvDef.compile_ext_call StateMachineMMIO.compilation_params;
    Pipeline.M := _;
    Pipeline.MM := _;
    Pipeline.RVM := MetricMinimalMMIO.IsRiscvMachine;
    Pipeline.PRParams := _
  |}.

  Global Instance Pipeline_assumptions : Pipeline.assumptions.
  Proof.
    constructor.
    { apply MMIO.word_riscv_ok. }
    { exact MMIO.funname_env_ok. }
    { exact MMIO.locals_ok. }
    { unfold Pipeline.PRParams, pipeline_params.
      eapply MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives. }
    { exact (@FlatToRiscv_hyps MMIO_compiler_params state_machine_params). }
    { exact (ext_spec_ok (p := @state_machine_params)). }
    { exact (compile_ext_call_correct (state_machine_parameters_ok:=state_machine_params_ok)). }
    { reflexivity. }
  Qed.

  Definition regs_initialized(regs: Registers): Prop :=
    forall r : Z, 0 < r < 32 -> exists v : word, map.get regs r = Some v.

  (* similar to compiler.LowerPipeline.machine_ok, but takes an `ExtraRiscvMachine D` instead of
     a `MetricRiscvMachine` *)
  Definition machine_ok(p_functions: word)(f_entry_rel_pos: Z)(stack_start stack_pastend: word)
             (finstrs: list Instruction)
             (p_call pc: word)(mH: mem)(Rdata Rexec: mem -> Prop)(mach: ExtraRiscvMachine D): Prop :=
      let CallInst := Jal RegisterNames.ra
                          (f_entry_rel_pos + word.signed (word.sub p_functions p_call)) : Instruction in
      (program RV32I p_functions finstrs *
       program RV32I p_call [CallInst] *
       LowerPipeline.mem_available stack_start stack_pastend *
       Rdata * Rexec * eq mH
      )%sep mach.(getMem) /\
      subset (footpr (program RV32I p_functions finstrs *
                      program RV32I p_call [CallInst] *
                      Rexec)%sep)
             (of_list (getXAddrs mach)) /\
      word.unsigned (mach.(getPc)) mod 4 = 0 /\
      mach.(getPc) = pc /\
      mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
      regs_initialized mach.(getRegs) /\
      map.get mach.(getRegs) RegisterNames.sp = Some stack_pastend /\
      (* Note: the concept of isMMIOAddr appears in the bedrock2 program specs, so it's
         fine if it also appears in the combined theorem *)
      map.undef_on mach.(getMem) StateMachineSemantics.parameters.isMMIOAddr /\
      disjoint (of_list mach.(getXAddrs)) StateMachineSemantics.parameters.isMMIOAddr.

  Lemma bedrock2_and_cava_system_correct: forall functions instrs pos_map required_stack_space
        f_entry_name fbody mc p_functions f_entry_rel_pos stack_start stack_pastend
        p_call mH Rdata Rexec (initialL: ExtraRiscvMachine D) steps_done postH,
      ExprImp.valid_funs functions ->
      compile functions = Some (instrs, pos_map, required_stack_space) ->
      map.get functions f_entry_name = Some ([], [], fbody) ->
      map.get pos_map f_entry_name = Some f_entry_rel_pos ->
      required_stack_space <= word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word ->
      word.unsigned (word.sub stack_pastend stack_start) mod bytes_per_word = 0 ->
      (exists s, StateMachineSemantics.parameters.is_initial_state s /\
                 device_state_related s initialL.(getExtraState)) ->
      Semantics.exec.exec functions fbody initialL.(getLog) mH map.empty mc
           (fun t' m' l' mc' => postH m' /\ exists s' tnew, t' = tnew ++ initialL.(getLog)
                                                            /\ execution tnew s') ->
      machine_ok p_functions f_entry_rel_pos stack_start stack_pastend instrs p_call
                 p_call mH Rdata Rexec initialL ->
      exists steps_remaining finalL mH',
        run_rec sched steps_done steps_remaining initialL = (Some tt, finalL) /\
        machine_ok p_functions f_entry_rel_pos stack_start stack_pastend instrs p_call
                   (word.add p_call (word.of_Z 4)) mH' Rdata Rexec finalL /\
        postH mH' /\
        finalL.(getLog) = initialL.(getLog) (* no external interactions happened *).
  Proof.
    intros.
    destruct initialL as (mach & d). destruct mach as [r pc npc m xAddrs t].
    unfold machine_ok in *; cbn -[map.get map.empty] in *. simp.
    edestruct (stateMachine_to_cava device_state_related)
      as (steps_remaining & finalL & finalH & Rn & Rfinal & Pf).
    2: {
      pose proof Pipeline.compiler_correct as P.
      unfold FlatToRiscvCommon.runsTo, GoFlatToRiscv.mcomp_sat,
        mcomp_sat, FlatToRiscvCommon.PRParams in P.
      cbn -[map.get map.empty] in P.
      eapply P with (initial := {| MetricRiscvMachine.getMachine := {| getPc := _ |} |});
        clear P; cbn -[map.get map.empty]; try eassumption.
      1: exact H6.
      unfold LowerPipeline.machine_ok; cbn -[map.get map.empty];
        ssplit; try eassumption; try reflexivity.
    }
    2: {
      inversion Rfinal. subst; clear Rfinal.
      unfold LowerPipeline.machine_ok in *. cbn -[map.get map.empty] in *.
      simp.
      eexists _, {| getMachine := {| getLog := t |} |}, _; cbn -[map.get map.empty]. ssplit.
      1: exact Rn.
      all: cbn -[map.get map.empty].
      all: try eassumption.
      all: try reflexivity.
    }
    (* `related` holds at beginning: *)
    change t with ([] ++ t) at 2.
    econstructor. 1: unfold execution. all: try eassumption.
    Unshelve.
    all: do 2 constructor.
  Qed.

End WithParams.
