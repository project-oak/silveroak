Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
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
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.SeparationLogic.
Require Import compiler.Pipeline.
Require Import compiler.LowerPipeline.
Require Import compiler.CompilerInvariant.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.StateMachineMMIOSpec.
Require Import Bedrock2Experiments.StateMachineMMIO.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Existing Instance SortedListString.map.
Existing Instance SortedListString.ok.

Section WithParams.
  Context {word : Interface.word.word 32} {word_ok: word.ok word}
          {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}
          {Registers: map.map Z word} {Registers_ok: map.ok Registers}
          {mem : Interface.map.map word Byte.byte} {mem_ok: map.ok mem}
          {M: state_machine.parameters} {M_ok: state_machine.ok M}
          {D: device}
          {DI: device_implements_state_machine D M}
          (sched: schedule).

  Open Scope ilist_scope.

  Definition regs_initialized(regs: Registers): Prop :=
    forall r : Z, 0 < r < 32 -> exists v : word, map.get regs r = Some v.

  (* similar to compiler.LowerPipeline.machine_ok, but takes an `ExtraRiscvMachine D` instead of
     a `MetricRiscvMachine`, and finstrs are bytes instead of Instructions *)
  Definition machine_ok(p_functions: word)(stack_start stack_pastend: word)
             (finstrs: list byte)(mH: mem)(Rdata Rexec: mem -> Prop)
             (mach: ExtraRiscvMachine D): Prop :=
      (ptsto_bytes p_functions finstrs *
       mem_available stack_start stack_pastend *
       Rdata * Rexec * eq mH
      )%sep mach.(getMem) /\
      subset (footpr (ptsto_bytes p_functions finstrs * Rexec)%sep)
             (of_list (getXAddrs mach)) /\
      word.unsigned (mach.(getPc)) mod 4 = 0 /\
      mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
      regs_initialized mach.(getRegs) /\
      map.get mach.(getRegs) RegisterNames.sp = Some stack_pastend /\
      device.is_ready_state mach.(getExtraState) /\
      (* Note: Even though we cancel out the fact that communication between the processor
         and the Cava device happens via MMIO, we still have to expose the fact that we
         need a reserved address range for MMIO which cannot be used as regular memory: *)
      map.undef_on mach.(getMem) device.isMMIOAddr /\
      disjoint (of_list mach.(getXAddrs)) device.isMMIOAddr.

  Lemma mod4_to_mod2: forall x, x mod 4 = 0 -> x mod 2 = 0.
  Proof. intros. Z.div_mod_to_equations. Lia.lia. Qed.

  Lemma bedrock2_and_cava_system_correct: forall fs instrs finfo required_stack_space
        f_entry_name p_functions f_entry_rel_pos stack_start stack_pastend argcount retcount
        ret_addr argvals mH Rdata Rexec (initialL: ExtraRiscvMachine D) steps_done postH,
      ExprImp.valid_funs (map.of_list fs) ->
      NoDup (map fst fs) ->
      compile compile_ext_call (map.of_list fs) = Some (instrs, finfo, required_stack_space) ->
      Forall (fun i : Instruction => verify i RV32IM) instrs ->
      map.get finfo f_entry_name = Some (argcount, retcount, f_entry_rel_pos) ->
      required_stack_space <= word.unsigned (word.sub stack_pastend stack_start) / 4 ->
      word.unsigned (word.sub stack_pastend stack_start) mod 4 = 0 ->
      word.unsigned p_functions mod 4 = 0 ->
      word.unsigned ret_addr mod 4 = 0 ->
      map.get initialL.(getRegs) RegisterNames.ra = Some ret_addr ->
      initialL.(getPc) = word.add p_functions (word.of_Z f_entry_rel_pos) ->
      WeakestPrecondition.call fs f_entry_name [] mH argvals
           (fun (t': Semantics.trace) (m': mem) (retvals: list word) =>
                            postH m' retvals /\
                            (* driver is supposed to put device back into initial state: *)
                            exists s', execution t' s' /\ state_machine.is_initial_state s') ->
      map.getmany_of_list initialL.(getRegs)
        (List.firstn argcount (reg_class.all reg_class.arg)) = Some argvals ->
      machine_ok p_functions stack_start stack_pastend (instrencode instrs)
                 mH Rdata Rexec initialL ->
      exists steps_remaining finalL mH' retvals,
        run_rec sched steps_done steps_remaining initialL = (Some tt, finalL) /\
        map.getmany_of_list finalL.(getRegs)
          (List.firstn retcount (reg_class.all reg_class.arg)) = Some retvals /\
        map.agree_on callee_saved initialL.(getRegs) finalL.(getRegs) /\
        finalL.(getPc) = ret_addr /\
        machine_ok p_functions stack_start stack_pastend (instrencode instrs)
                   mH' Rdata Rexec finalL /\
        postH mH' retvals.
  Proof.
    intros.
    destruct initialL as (mach & d). destruct mach as [r pc npc m xAddrs t].
    unfold machine_ok in *; cbn -[map.get map.empty instrencode] in *. simp.
    replace device.isMMIOAddr with state_machine.isMMIOAddr in *. 2: {
      symmetry. extensionality x. apply propositional_extensionality. unfold iff.
      pose proof mmioAddrs_match as P. unfold sameset, subset in P.
      clear -P. unfold elem_of, device.isMMIOAddr in *. destruct P. eauto.
    }
    edestruct stateMachine_to_cava
      as (steps_remaining & finalL & finalH & Rn & Rfinal & Pf).
    2: {
      pose proof Pipeline.compiler_correct_wp as P.
      unfold FlatToRiscvCommon.runsTo, GoFlatToRiscv.mcomp_sat, mcomp_sat in P.
      cbn -[map.get map.empty instrencode reg_class.all] in P.
      specialize P with (ret_addr := ret_addr) (p_funcs := p_functions).
      eapply P with (initial := {| MetricRiscvMachine.getMachine := {| getPc := _ |} |});
        clear P; cbn -[map.get map.empty instrencode reg_class.all]; try eassumption.
      { apply compile_ext_call_correct. }
      { intros. reflexivity. }
      { reflexivity. }
      unfold LowerPipeline.machine_ok; cbn -[map.get map.empty instrencode program reg_class.all].
      pose proof ptsto_bytes_to_program (iset := RV32IM) as P.
      match goal with
      | |- context[?Q] => lazymatch Q with
                          | program _ ?p ?i => replace Q with (ptsto_bytes p (instrencode i))
                          end
      end.
      2: { eapply iff1ToEq. eapply P; eassumption. }
      subst.
      ssplit; try eassumption; try reflexivity.
    }
    2: {
      inversion Rfinal. subst; clear Rfinal.
      unfold LowerPipeline.machine_ok in *.
      cbn -[map.get map.empty instrencode reg_class.all] in *.
      simp.
      eexists _, {| getMachine := {| getLog := _ |} |}, _, retvals.
      cbn -[map.get map.empty instrencode reg_class.all].
      split. 1: exact Rn.
      pose proof ptsto_bytes_to_program (iset := RV32IM) as P. cbn in P.
      match goal with
      | |- context[?Q] => lazymatch Q with
                          | ptsto_bytes ?p (instrencode ?i) => replace Q with (program RV32IM p i)
                          end
      end.
      2: { eapply iff1ToEq. symmetry. eapply P; eassumption. }
      ssplit.
      all: cbn -[map.get map.empty instrencode reg_class.all].
      all: try eassumption.
      all: try reflexivity.
      match goal with
      | E1: execution _ _, E2: execution _ _ |- _ =>
        pose proof (execution_unique _ _ _ E1 E2); subst; clear E2
      end.
      eauto using initial_state_is_ready_state.
    }
    (* `related` holds at beginning: *)
    subst pc.
    edestruct initial_state_exists as (sH & ? & ?). 1: eassumption.
    eapply mkRelated; simpl; eauto.
    Unshelve.
    all: do 2 constructor.
  Qed.

End WithParams.
