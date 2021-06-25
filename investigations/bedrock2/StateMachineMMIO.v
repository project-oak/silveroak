Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Macros.unique.
Require Import compiler.util.Common.
Require Import bedrock2.Semantics.
Require Import riscv.Utility.Monads.
Require Import compiler.FlatImp.
Require Import riscv.Spec.Decode.
Require Import coqutil.sanity.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Machine.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvFunctions.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricMinimalMMIO.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatToRiscvDef.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import coqutil.Datatypes.Option.
Require Import coqutil.Z.HexNotation.
Require Import coqutil.Tactics.Simp.
Require Import compiler.util.Learning.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.RiscvWordProperties.
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Datatypes.ListSet.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.LibBase.MMIOLabels.
Import ListNotations.

Open Scope ilist_scope.

(* Based on bedrock2's compilerExamples/MMIO.v *)

Definition compile_write(action: string): Z -> Z -> Z -> Instruction :=
  (* this file assumes a 32-bit architecture, so WRITEW is the same as WRITE32, and all
     other action strings are excluded by ext_spec, so we can return Sw in all these cases *)
  if String.eqb action WRITE8 then Sb else if String.eqb action WRITE16 then Sh else Sw.

Definition compile_read(action: string): Z -> Z -> Z -> Instruction :=
  (* this file assumes a 32-bit architecture, so READW is the same as READ32, and all
     other action strings are excluded by ext_spec, so we can return Lw in all these cases *)
  if String.eqb action READ8 then Lb else if String.eqb action READ16 then Lh else Lw.

Definition compile_ext_call(results: list Z) a (args: list Z):
  list Instruction :=
  if String.prefix WRITE_PREFIX a then
    match results, args with
    | [], [addr; val] => [[ compile_write a addr val 0 ]]
    | _, _ => [[]] (* invalid, excluded by ext_spec *)
    end
  else
    match results, args with
    | [res], [addr] => [[ compile_read a res addr 0 ]]
    | _, _ => [[]] (* invalid, excluded by ext_spec *)
    end.

Lemma compile_write_not_Invalid: forall action rd rs ofs,
  not_InvalidInstruction (compile_write action rd rs ofs).
Proof.
  unfold not_InvalidInstruction, compile_write.
  intros.
  repeat match goal with
         | |- context[String.eqb ?a ?b] => destr (String.eqb a b)
         end;
    exact I.
Qed.

Lemma compile_read_not_Invalid: forall action rd rs ofs,
  not_InvalidInstruction (compile_read action rd rs ofs).
Proof.
  unfold not_InvalidInstruction, compile_read.
  intros.
  repeat match goal with
         | |- context[String.eqb ?a ?b] => destr (String.eqb a b)
         end;
    exact I.
Qed.

Module Import MMIO.
  Class parameters := {
    word :> Word.Interface.word 32;
    word_ok :> word.ok word;
    word_riscv_ok :> word.riscv_ok word;
    mem :> map.map word byte;
    mem_ok :> map.ok mem;
    locals :> map.map Z word;
    locals_ok :> map.ok locals;
    funname_env :> forall T, map.map String.string T;
    funname_env_ok :> forall T, map.ok (funname_env T);
  }.
End MMIO.

Section MMIO1.
  Context {p: unique! MMIO.parameters}.
  Context {state_machine_parameters :
             StateMachineSemantics.parameters 32 MMIO.word MMIO.mem}
          {state_machine_parameters_ok :
             StateMachineSemantics.parameters.ok state_machine_parameters}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Instance Words32: Utility.Words := {
    Utility.word := word;
    Utility.width_cases := or_introl eq_refl;
  }.

  Instance compilation_params: FlatToRiscvDef.parameters := {|
    FlatToRiscvDef.iset := RV32I;
    FlatToRiscvDef.compile_ext_call _ _ _ s :=
      match s with
      | SInteract resvars action argvars => compile_ext_call resvars action argvars
      | _ => []
      end;
  |}.

  Instance StateMachineMMIOSpec : MMIOSpec :=
    {| isMMIOAddr := parameters.isMMIOAddr;
       isMMIOAligned n a := word.unsigned a mod (Z.of_nat n) = 0;
       MMIOReadOK :=
         fun n log addr val =>
           exists s s' r sz,
             Memory.bytes_per (width := width) sz = n
             /\ execution log s
             /\ parameters.reg_addr r = addr
             /\ parameters.read_step sz s r val s'
    |}.

  Instance FlatToRiscv_params: FlatToRiscvCommon.parameters := {
    FlatToRiscvCommon.def_params := compilation_params;
    FlatToRiscvCommon.locals := locals;
    FlatToRiscvCommon.mem := (@mem p);
    FlatToRiscvCommon.MM := free.Monad_free;
    FlatToRiscvCommon.RVM := MetricMinimalMMIO.IsRiscvMachine;
    FlatToRiscvCommon.PRParams := MetricMinimalMMIOPrimitivesParams;
    FlatToRiscvCommon.ext_spec := StateMachineSemantics.ext_spec;
  }.

  Lemma load_bytes_in_MMIO_is_None: forall n (m: mem) (addr: word),
      map.undef_on m isMMIOAddr ->
      isMMIOAddr addr ->
      Memory.load_bytes (S n) m addr = None.
  Proof.
    intros. unfold Memory.load_bytes, map.undef_on, map.agree_on, map.getmany_of_tuple in *.
    simpl.
    rewrite H by assumption.
    rewrite map.get_empty.
    reflexivity.
  Qed.

  Ltac contrad := contradiction || discriminate || congruence.

  (* TODO: why are these here? *)
  Arguments LittleEndian.combine: simpl never. (* TODO can we put this next to its definition? *)
  Arguments mcomp_sat: simpl never.
  Arguments LittleEndian.split: simpl never.
  Local Arguments String.eqb: simpl never.
  (* give it priority over FlatToRiscvCommon.FlatToRiscv.PRParams to make eapply work better *)
  Existing Instance MetricMinimalMMIOPrimitivesParams.
  Existing Instance MetricMinimalMMIOSatisfiesPrimitives.
  Local Existing Instance MetricMinimalMMIOSatisfiesPrimitives.

  Ltac fwd :=
    match goal with
    |- free.interp interp_action ?p ?s ?post =>
      let p' := eval hnf in p in
      change (free.interp interp_action p' s post);
      rewrite free.interp_act;
      cbn [interp_action MinimalMMIO.interpret_action snd fst];
        simpl_MetricRiscvMachine_get_set
    | |- load ?n ?ctx ?a ?s ?k =>
        let g' := eval cbv beta delta [load] in (load n ctx a s k) in
        change g';
        simpl_MetricRiscvMachine_get_set
    | _ => progress cbn [free.bind]
    | |- store ?n ?ctx ?a ?v ?s ?k =>
        let g' := eval cbv beta delta [store] in (store n ctx a v s k) in
        change g';
        simpl_MetricRiscvMachine_get_set
    | _ => progress cbn [free.bind]
    | _ => rewrite free.interp_ret
    end.

  Lemma disjoint_MMIO_goal: forall (x y: word),
      isMMIOAddr x ->
      ~ isMMIOAddr y ->
      x <> y.
  Proof.
    intros x y Hx Hy C. subst. apply Hy. apply Hx.
  Qed.

  Instance FlatToRiscv_hyps: FlatToRiscvCommon.assumptions.
  Proof.
    constructor.
    - reflexivity.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - eapply MetricMinimalMMIOSatisfiesPrimitives; cbn; intuition eauto.
  Qed.

  Ltac simpl_paramrecords :=
    change (@FlatToRiscvCommon.W FlatToRiscv_params) with Words32 in *;
    change (@FlatToRiscvCommon.locals FlatToRiscv_params) with (@locals p) in *;
    change (@FlatToRiscvCommon.mem FlatToRiscv_params) with (@mem p) in *;
    change (@width Words32) with 32 in *;
    change (@Utility.word Words32) with (@word p) in *.

  Lemma execute_compile_write sz rs1 rs2 a v initial (post: unit -> MetricRiscvMachine -> Prop):
      valid_FlatImp_var rs1 ->
      valid_FlatImp_var rs2 ->
      map.get (getRegs (getMachine initial)) rs1 = Some a ->
      map.get (getRegs (getMachine initial)) rs2 = Some v ->
      isMMIOAddr a ->
      word.unsigned a mod Z.of_nat (bytes_per (width := width) sz) = 0 ->
      map.undef_on (getMem (getMachine initial)) isMMIOAddr ->
      post tt (withXAddrs (invalidateWrittenXAddrs (Memory.bytes_per (width := width) sz) a
                                                   (getXAddrs initial))
              (withLogItem (mmioStoreEvent a
                    (LittleEndian.split (Memory.bytes_per (width := width) sz) (word.unsigned v)))
              (updateMetrics (addMetricStores 1)
              initial))) ->
      free.interp interp_action (Execute.execute
                                   (compile_write (access_size_to_MMIO_write sz) rs1 rs2 0))
                  initial post.
  Proof.
    intros.
    destruct sz; repeat fwd;
      repeat match goal with
             | |- context [Z.eq_dec ?r 0] => destruct (Z.eq_dec r 0);
                                             cbv [valid_FlatImp_var] in *; [exfalso; blia|]
             | H: ?m = Some _ |- context [match ?m with _ => _ end] => rewrite H
             | |- _ => progress (cbv [Utility.add Utility.ZToReg MachineWidth_XLEN]; rewrite add_0_r)
             | |- _ => progress (unfold Memory.store_bytes;
                                 rewrite load_bytes_in_MMIO_is_None by assumption)
             | |- _ => progress cbv [MinimalMMIO.nonmem_store StateMachineMMIOSpec]
             | |- _ => progress cbn -[invalidateWrittenXAddrs]
             | |- _ /\ _ => split; auto
             | |- _ => destruct initial; assumption
             end.
  Qed.

  Lemma execute_compile_read sz rd rs a initial (post: unit -> MetricRiscvMachine -> Prop):
      valid_FlatImp_var rd ->
      valid_FlatImp_var rs ->
      map.get (getRegs (getMachine initial)) rs = Some a ->
      isMMIOAddr a ->
      word.unsigned a mod Z.of_nat (bytes_per (width := width) sz) = 0 ->
      map.undef_on (getMem (getMachine initial)) isMMIOAddr ->
      (forall v,
          post tt (withLogItem (mmioLoadEvent a v)
                  (updateMetrics (addMetricLoads 1)
                  (withRegs
                     (map.put (getRegs initial) rd
                              (word.of_Z (signExtend 32 (LittleEndian.combine 4 v))))
                     initial)))) ->
      free.interp interp_action (Execute.execute
                                   (compile_read (access_size_to_MMIO_write sz) rd rs 0))
                  initial post.
  Proof.
    intros.
    destruct sz; repeat fwd;
      repeat match goal with
             | |- context [Z.eq_dec ?r 0] => destruct (Z.eq_dec r 0);
                                             cbv [valid_FlatImp_var] in *; [exfalso; blia|]
             | H: ?m = Some _ |- context [match ?m with _ => _ end] => rewrite H
             | |- _ => progress (cbv [Utility.add Utility.ZToReg MachineWidth_XLEN]; rewrite add_0_r)
             | |- _ => progress (unfold Memory.store_bytes;
                                 rewrite load_bytes_in_MMIO_is_None by assumption)
             | |- _ => progress cbv [MinimalMMIO.nonmem_load StateMachineMMIOSpec]
             | |- _ => progress cbn -[invalidateWrittenXAddrs HList.tuple] in *
             | |- _ /\ _ => split; auto
             | |- Execute = Fetch -> _ => discriminate
             | |- _ => destruct initial; solve [eauto]
             | |- _ => progress (intros; simp)
             end.
  Admitted.

  Axiom TODO: False.

  Lemma compile_ext_call_correct: forall resvars extcall argvars,
      FlatToRiscvCommon.compiles_FlatToRiscv_correctly
        (@FlatToRiscvDef.compile_ext_call compilation_params)
        (FlatImp.SInteract resvars extcall argvars).
  Proof.
    unfold FlatToRiscvCommon.compiles_FlatToRiscv_correctly.
    simpl. intros.
    destruct H5 as [V_resvars V_argvars].
    rename extcall into action.
    simp.
    destruct_RiscvMachine initialL.
    unfold compile_ext_call, FlatToRiscvCommon.goodMachine in *.
    match goal with
    | H: forall _ _, outcome _ _ -> _ |- _ => specialize H with (mReceive := map.empty)
    end.
    destruct (String.prefix WRITE_PREFIX action) eqn: E;
      cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics getXAddrs] in *.
    + (* MMOutput *)
      progress simpl in *|-.
      match goal with
      | H: StateMachineSemantics.ext_spec _ _ _ _ _ |- _ => rename H into Ex
      end.
      cbv [FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec ] in Ex.
      cbv [ext_spec FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec
                    StateMachineSemantics.ext_spec] in Ex.
      simpl in *|-.
      rewrite E in *.
      logical_simplify. subst mGive argvals.
      destruct argvars. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn in *; congruence
        end.
      }
      destruct argvars. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn in *; destruct_one_match_hyp; congruence
        end.
      }
      destruct argvars; cycle 1. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn in *; simp; destruct_one_match_hyp; congruence
        end.
      }
      cbn -[String.append] in *|-.
      match goal with
      | H: map.split _ _ map.empty |- _ => rewrite map.split_empty_r in H; subst
      end.
      match goal with
      | HO : forall _ _ :  parameters.state, _ |- _ =>
        specialize (HO _ _ ltac:(eassumption) ltac:(eassumption))
      end.
      match goal with
      | HO: outcome _ _, H: _ |- _ => specialize (H _ HO); rename H into HP
      end.
      destruct g. cbn [
           FlatToRiscvCommon.p_sp
           FlatToRiscvCommon.rem_stackwords
           FlatToRiscvCommon.rem_framewords
           FlatToRiscvCommon.p_insts
           FlatToRiscvCommon.insts
           FlatToRiscvCommon.program_base
           FlatToRiscvCommon.e_pos
           FlatToRiscvCommon.e_impl
           FlatToRiscvCommon.dframe
           FlatToRiscvCommon.xframe ] in *.
      simp.
      subst.
      cbn -[String.append] in *.
      simp.
      eapply runsToNonDet.runsToStep_cps.

      eapply go_fetch_inst with (inst := (compile_write (access_size_to_MMIO_write x2) z z0 0));
        simpl_MetricRiscvMachine_get_set; cbn -[String.append] in *.
      1: reflexivity.
      { eapply rearrange_footpr_subset. 1: eassumption. wwcancel. }
      { wcancel_assumption. }
      { eapply compile_write_not_Invalid. }
      unfold mcomp_sat, Primitives.mcomp_sat, MetricMinimalMMIOPrimitivesParams.

      eapply free.interp_bind. 1: eapply interp_action_weaken_post.
      eapply execute_compile_write; cbn -[String.append]; try eassumption;
        repeat lazymatch goal with
               | Hext : map.extends initialL_regs ?l, Hget : map.get ?l ?k = Some ?x
                 |- context [map.get initialL_regs ?k] =>
                 replace (map.get initialL_regs k) with (Some x)
                   by (symmetry; unfold map.extends in Hext; eauto)
               end;
        try reflexivity.
      { eauto using parameters.write_step_isMMIOAddr. }
      { eauto using parameters.write_step_is_aligned. }

      eapply runsToNonDet.runsToDone.
      simpl_MetricRiscvMachine_get_set.
      simpl_word_exprs word_ok.
      unfold mmioStoreEvent, signedByteTupleToReg in *.
      unfold regToInt32.
      rewrite LittleEndian.combine_split.
      match goal with
      | |- context [signExtend ?w (?x mod ?y)] =>
        replace (signExtend w (x mod y)) with x
      end. 2: {
        (* mismatch: bedrock2.Semantics and compiler.FlatImp semantics put values of external calls
           into trace without signExtending (they don't get any access_size param that would allow
           them to do so), whereas the RISC-V machine does sign extend them! *)
        case TODO.
      }
      rewrite word.of_Z_unsigned.
      cbn -[invalidateWrittenXAddrs String.append] in *.
      specialize (HPp1 mKeep). rewrite map.split_empty_r in HPp1. specialize (HPp1 eq_refl).
      do 4 eexists.
      split; eauto.
      split; eauto.
      split; [unfold map.only_differ; eauto|].
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split. {
        lazymatch goal with
        | H: map.undef_on initialL_mem ?A |- _ =>
          rename H into U; change (map.undef_on initialL_mem isMMIOAddr) in U; move U at bottom
        end.
        lazymatch goal with
        | H: disjoint (of_list initialL_xaddrs) ?A |- _ =>
          rename H into D; change (disjoint (of_list initialL_xaddrs) isMMIOAddr) in D;
            move D at bottom
        end.
        assert (forall {T: Type} (a b c: set T), subset a b -> subset b c -> subset a c)
          as subset_trans. {
          clear. unfold subset, PropSet.elem_of. intros. firstorder idtac.
        }
        eapply subset_trans. 1: eassumption.
        assert (isMMIOAddr (parameters.reg_addr x)) as IM. {
          eapply parameters.write_step_isMMIOAddr. eassumption.
        }
        clear -(*D4 M0*) IM D state_machine_parameters_ok.
        destruct x2; change (bytes_per Syntax.access_size.word) with 4%nat; cbn.
        all:change removeXAddr with (@List.removeb word word.eqb _).
        all:rewrite ?ListSet.of_list_removeb.
        all:unfold map.undef_on, map.agree_on, disjoint in *.
        all:unfold subset, diff, singleton_set, of_list, PropSet.elem_of in *.
        all:intros y HIn.
        all:specialize (D y); destruct D; [contradiction|].
        all:rewrite ?and_assoc.
        all:split; [exact HIn|clear HIn].
        all:pose proof (word.unsigned_range (parameters.reg_addr x)).
        all:ssplit; eapply disjoint_MMIO_goal; eauto.
        all:case TODO. (*
        all:cbv [isMMIOAddr StateMachineMMIOSpec].
        all:exists (parameters.reg_addr x).
        all:split; [ exact IR | ].
        all:simpl_paramrecords.
        all:push_unsigned.
        all:auto with zarith. }
        *) }
      replace "MMIOWRITE"%string with (access_size_to_MMIO_write x2). 2: {
        case TODO. (* needs update in riscv-coq *)
      }
      ssplit; eauto.
      destruct x2; change (bytes_per Syntax.access_size.word) with 4%nat; cbn.
      all:change removeXAddr with (@List.removeb word word.eqb _).
      all:rewrite ?ListSet.of_list_removeb.
      all:repeat apply disjoint_diff_l.
      all:assumption.

    + (* MMInput *)
      simpl in *|-.
      match goal with
      | H: StateMachineSemantics.ext_spec _ _ _ _ _ |- _ => rename H into Ex
      end.
      cbv [FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec ] in Ex.
      cbv [ext_spec FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec
                    StateMachineSemantics.ext_spec] in Ex.
      simpl in *|-.

      rewrite E in *.
      destruct (String.prefix READ_PREFIX action) eqn: EE; try contradiction.
      logical_simplify; subst.
      repeat match goal with
             | l: list _ |- _ => destruct l;
                                 try (exfalso; (contrad || (cheap_saturate; contrad))); []
             end.
      destruct argvars; cycle 1. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn -[String.append] in *; simp; destruct_one_match_hyp; congruence
        end.
      }
      cbn -[String.append] in *|-.
      match goal with
      | H: map.split _ _ map.empty |- _ => rewrite map.split_empty_r in H; subst
      end.
      destruct g. cbn [
           FlatToRiscvCommon.p_sp
           FlatToRiscvCommon.rem_stackwords
           FlatToRiscvCommon.rem_framewords
           FlatToRiscvCommon.p_insts
           FlatToRiscvCommon.insts
           FlatToRiscvCommon.program_base
           FlatToRiscvCommon.e_pos
           FlatToRiscvCommon.e_impl
           FlatToRiscvCommon.dframe
           FlatToRiscvCommon.xframe ] in *.
      simp.
      subst.
      cbn -[String.append] in *.
      eapply runsToNonDet.runsToStep_cps.

      eapply go_fetch_inst with (inst := (compile_read (access_size_to_MMIO_read x1) z0 z 0));
        simpl_MetricRiscvMachine_get_set; cbn -[String.append] in *.
      1: reflexivity.
      { eapply rearrange_footpr_subset. 1: eassumption. wwcancel. }
      { wcancel_assumption. }
      { eapply compile_read_not_Invalid. }
      unfold mcomp_sat, Primitives.mcomp_sat, MetricMinimalMMIOPrimitivesParams.

      eapply free.interp_bind. 1: eapply interp_action_weaken_post.
      eapply execute_compile_read; cbn -[String.append]; try eassumption;
        repeat lazymatch goal with
               | Hext : map.extends initialL_regs ?l, Hget : map.get ?l ?k = Some ?x
                 |- context [map.get initialL_regs ?k] =>
                 replace (map.get initialL_regs k) with (Some x)
                   by (symmetry; unfold map.extends in Hext; eauto)
               end;
        try reflexivity.
      { eauto using parameters.write_step_isMMIOAddr. }
      { eauto using parameters.write_step_is_aligned. }

      split; simpl_MetricRiscvMachine_get_set. {
        intros _.
        eapply ptsto_instr_subset_to_isXAddr4.
        eapply shrink_footpr_subset. 1: eassumption.
        unfold program.
        cbn in *. wwcancel.
      }
      erewrite ptsto_bytes.load_bytes_of_sep; cycle 1.
      { cbv [program ptsto_instr Scalars.truncated_scalar Scalars.littleendian] in *.
        cbn [array bytes_per] in *.
        simpl_MetricRiscvMachine_get_set.
        wcancel_assumption. }

      change (@Bind (@FlatToRiscvCommon.M FlatToRiscv_params) (@FlatToRiscvCommon.MM FlatToRiscv_params))
        with (@free.bind MetricMinimalMMIO.action result) in *.
      unfold free.bind at 1.

      rewrite LittleEndian.combine_split.
      rewrite Z.mod_small by (eapply EncodeBound.encode_range).
      rewrite DecodeEncode.decode_encode; cycle 1. {
        unfold valid_instructions, FlatToRiscvDef.iset in *. cbn in *. eauto.
      }

      repeat fwd.

      destruct (Z.eq_dec z 0); cbv [valid_FlatImp_var] in *; [exfalso; blia|].
      destruct (Z.eq_dec z0 0); cbv [valid_FlatImp_var] in *; [exfalso; blia|].
      simpl_paramrecords.
      repeat lazymatch goal with
             | Hext : map.extends initialL_regs ?l, Hget : map.get ?l ?k = Some ?x
               |- context [map.get initialL_regs ?k] =>
               replace (map.get initialL_regs k) with (Some x) by (symmetry; unfold map.extends in Hext; eauto)
             end.

      split; try discriminate.
      cbv [Utility.add Utility.ZToReg MachineWidth_XLEN]; rewrite add_0_r.
      unshelve erewrite (_ : _ = None). {
        eapply loadWord_in_MMIO_is_None. 1: eassumption.
        cbn. eexists. split; [eauto using parameters.read_step_is_reg_addr|blia].
      }

      cbv [MinimalMMIO.nonmem_load StateMachineMMIOSpec].
      split. {
        cbn. eexists. split; [eauto using parameters.read_step_is_reg_addr|blia].
      }
      split; [red; eauto using parameters.read_step_is_reg_addr, parameters.reg_addrs_aligned|].
      split.
      { cbv [MMIOReadOK].
        let val := lazymatch goal with
                   | H : parameters.read_step _ _ ?val _ |- _ => val end in
        (exists (LittleEndian.split 4 (word.unsigned val))).
        cbv [signedByteTupleToReg].
        rewrite LittleEndian.combine_split.
        rewrite Z.mod_small by apply word.unsigned_range.
        rewrite sextend_width_nop by reflexivity.
        rewrite word.of_Z_unsigned.
        eauto 10. }
      intros.

      repeat fwd.

      eapply runsToNonDet.runsToDone.
      simpl_MetricRiscvMachine_get_set.
      simpl_word_exprs word_ok.

      (* simplify MMIOReadOK precondition *)
      lazymatch goal with
      | H : MMIOReadOK _ _ _ _ |- _ =>
        cbv [MMIOReadOK] in H; cbn [getLog] in H
      end.
      logical_simplify; subst.
      lazymatch goal with
      | H : parameters.reg_addr _ = parameters.reg_addr _ |- _ =>
        apply parameters.reg_addr_unique in H; subst
      end.
      lazymatch goal with
      | HO : forall _ _ v, _ -> parameters.read_step _ _ v _ -> _ |- _ =>
        specialize (HO _ _ (signedByteTupleToReg _) ltac:(eassumption) ltac:(eassumption))
      end.

      unfold mmioLoadEvent, signedByteTupleToReg.
      match goal with
      | HO: outcome _ _, H: _ |- _ => specialize (H _ HO); rename H into P
      end.
      cbn in P.
      simp.
      apply eqb_eq in EE. subst action.
      cbn in *.
      specialize (Pp1 mKeep). rewrite map.split_empty_r in Pp1. specialize (Pp1 eq_refl).
      destruct (Z.eq_dec z0 0); try contradiction.
      do 4 eexists.
      split; eauto.
      split; eauto.
      split. {
        unfold map.only_differ. intros. unfold union, of_list, elem_of, singleton_set. simpl.
        rewrite map.get_put_dec.
        destruct_one_match; auto.
      }
      split. {
        eapply map.put_extends. eassumption.
      }
      split. {
        intros.
        match goal with
        | H : context [map.get _ ?x] |- _ <= ?x < _ =>
          rewrite map.get_put_dec in H
        end.
        destruct_one_match_hyp. 1: blia. eauto.
      }
      split. {
        rewrite map.get_put_diff; eauto. unfold RegisterNames.sp. blia.
      }
      split. {
        eapply @FlatToRiscvCommon.preserve_regs_initialized_after_put.
        2: eassumption.
        typeclasses eauto.
      }
      eauto 10.
  Time Qed. (* takes ~30s *)

End MMIO1.

Existing Instance Words32.
Existing Instance semantics_parameters.
Existing Instance compilation_params.
Existing Instance FlatToRiscv_params.
Existing Instance FlatToRiscv_hyps.
