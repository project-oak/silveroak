Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Datatypes.PropSet.
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
          (sched: schedule).

  Open Scope ilist_scope.

  Global Instance MMIO_compiler_params: StateMachineMMIO.MMIO.parameters := {|
    MMIO.word := word;
    MMIO.word_ok := _;
    MMIO.word_riscv_ok := _;
    MMIO.mem := SortedListWord.map _ _;
    MMIO.mem_ok := _;
    MMIO.locals := _;
    MMIO.locals_ok := _;
    MMIO.funname_env := SortedListString.map;
    MMIO.funname_env_ok := SortedListString.ok;
  |}.

  Global Instance pipeline_params: Pipeline.parameters := {|
    Pipeline.W := _;
    Pipeline.mem := _;
    Pipeline.Registers := _;
    Pipeline.string_keyed_map := _;
    Pipeline.ext_spec := StateMachineSemantics.ext_spec;
    Pipeline.compile_ext_call :=
      @FlatToRiscvDef.FlatToRiscvDef.compile_ext_call StateMachineMMIO.compilation_params;
    Pipeline.M := _;
    Pipeline.MM := _;
    Pipeline.RVM := MetricMinimalMMIO.IsRiscvMachine;
    Pipeline.PRParams := _
  |}.

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
      map.get mach.(getRegs) RegisterNames.sp = Some stack_pastend (*/\
      TODO we should have some conditions that imply these, but don't use the notion of
      MMIO, because MMIO is only used at the intermediate spec that we want to cancel out
      map.undef_on m StateMachineSemantics.parameters.isMMIOAddr /\
      disjoint (of_list xAddrs) StateMachineSemantics.parameters.isMMIOAddr *) .

  Lemma bedrock2_and_cava_system_correct: forall functions instrs pos_map required_stack_space
        f_entry_name fbody mc p_functions f_entry_rel_pos stack_start stack_pastend
      finstrs p_call mH Rdata Rexec (initialL: ExtraRiscvMachine D) steps_done postH,
      ExprImp.valid_funs functions ->
      compile functions = Some (instrs, pos_map, required_stack_space) ->
      map.get functions f_entry_name = Some ([], [], fbody) ->
      map.get pos_map f_entry_name = Some f_entry_rel_pos ->
      required_stack_space <= word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word ->
      Semantics.exec.exec functions fbody initialL.(getLog) mH map.empty mc
           (fun t' m' l' mc' => postH m') ->
      machine_ok p_functions f_entry_rel_pos stack_start stack_pastend finstrs p_call
                 p_call mH Rdata Rexec initialL ->
      exists steps_remaining finalL mH',
        run_rec sched steps_done steps_remaining initialL = (Some tt, finalL) /\
        machine_ok p_functions f_entry_rel_pos stack_start stack_pastend finstrs p_call
                   (word.add p_call (word.of_Z 4)) mH' Rdata Rexec finalL /\
        postH mH'.
  Proof.
    intros.
    pose proof @Pipeline.compiler_correct as P.
    pose proof stateMachine_to_cava as Q.
  Admitted.

End WithParams.
