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
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Import ListNotations.

Open Scope ilist_scope.

(* Based on bedrock2's compilerExamples/MMIO.v *)

Definition compile_ext_call(results: list Z) a (args: list Z):
  list Instruction :=
  if String.eqb a WRITE then
    match results, args with
    | [], [addr; val] => [[ Sw addr val 0 ]]
    | _, _ => [[]] (* invalid, excluded by ext_spec *)
    end
  else
    match results, args with
    | [res], [addr] => [[ Lw res addr 0 ]]
    | _, _ => [[]] (* invalid, excluded by ext_spec *)
    end.

Lemma compile_ext_call_length: forall binds f args,
    Z.of_nat (List.length (compile_ext_call binds f args)) <= 1.
Proof.
  intros. unfold compile_ext_call.
  destruct (String.eqb _ _); destruct binds; try destruct binds;
  try destruct args; try destruct args; try destruct args;
  cbv; intros; discriminate.
Qed.

Lemma compile_ext_call_length': forall binds f args,
    Z.of_nat (List.length (compile_ext_call binds f args)) <= 7.
Proof. intros. rewrite compile_ext_call_length. blia. Qed.

Lemma compile_ext_call_emits_valid: forall iset binds a args,
    Forall valid_FlatImp_var binds ->
    Forall valid_FlatImp_var args ->
    valid_instructions iset (compile_ext_call binds a args).
Proof.
  intros.
  unfold compile_ext_call.
  destruct (String.eqb _ _); destruct args; try destruct args; try destruct args;
    destruct binds; try destruct binds;
    intros instr HIn; cbn -[String.eqb] in *; intuition idtac; try contradiction.
  - rewrite <- H1.
    simp_step.
    simp_step.
    (* try simp_step. (* TODO this should not fail fatally *) *)
    split; [|cbv;auto].
    unfold Encode.respects_bounds. simpl.
    unfold Encode.verify_S, valid_FlatImp_var, opcode_STORE, funct3_SW in *.
    repeat split; (blia || assumption).
  - rewrite <- H1.
    simp_step.
    simp_step.
    simp_step.
    simp_step.
    (* try simp_step. (* TODO this should not fail fatally *) *)
    split; [|cbv;auto].
    unfold Encode.respects_bounds. simpl.
    unfold Encode.verify_I, valid_FlatImp_var, opcode_LOAD, funct3_LW in *.
    repeat split; (blia || assumption).
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
  Context {consts : constants word.rep} {consts_ok : constants_ok consts}
          {circuit_spec : circuit_behavior}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Instance Words32: Utility.Words := {
    Utility.word := word;
    Utility.width_cases := or_introl eq_refl;
  }.

  Instance semantics_params : IncrementWaitSemantics.parameters := {|
    IncrementWaitSemantics.parameters.word := word;
    IncrementWaitSemantics.parameters.mem := mem |}.

  Instance semantics_params_ok : IncrementWaitSemantics.parameters.ok _ := {|
    IncrementWaitSemantics.parameters.word_ok := _;
    IncrementWaitSemantics.parameters.mem_ok := _ |}.

  Instance compilation_params: FlatToRiscvDef.parameters := {|
    FlatToRiscvDef.iset := RV32I;
    FlatToRiscvDef.compile_ext_call _ _ _ s :=
      match s with
      | SInteract resvars action argvars => compile_ext_call resvars action argvars
      | _ => []
      end;
  |}.

  Instance IncrementWaitMMIOSpec : MMIOSpec :=
    {| isMMIOAddr :=
         fun w =>
           Exists (fun addr => word.unsigned addr <= word.unsigned w <= word.unsigned addr + 4) reg_addrs;
       isMMIOAligned := fun n addr => n = 4%nat /\ (word.unsigned addr) mod 4 = 0;
       MMIOReadOK :=
         fun n log addr val =>
           exists s s' r,
             execution log s
             /\ reg_addr r = addr
             /\ read_step s r val s'
    |}.

  Instance FlatToRiscv_params: FlatToRiscvCommon.parameters := {
    FlatToRiscvCommon.def_params := compilation_params;
    FlatToRiscvCommon.locals := locals;
    FlatToRiscvCommon.mem := (@mem p);
    FlatToRiscvCommon.MM := free.Monad_free;
    FlatToRiscvCommon.RVM := MetricMinimalMMIO.IsRiscvMachine;
    FlatToRiscvCommon.PRParams := MetricMinimalMMIOPrimitivesParams;
    FlatToRiscvCommon.ext_spec := IncrementWaitSemantics.ext_spec (p:=semantics_params);
  }.

  Section CompilationTest.
    Definition magicMMIOAddrLit: Z := Ox"10024000".
    Variable addr: Z.
    Variable i: Z.
    Variable s: Z.

    (*
    addr = magicMMIOAddr;
    loop {
      i = input addr;
      stay in loop only if i is non-zero;
      s = i _ i;
      output addr s;
    }
    *)
    Definition doubler: stmt Z :=
      (SSeq (SLit addr magicMMIOAddrLit)
            (SLoop (SLoad Syntax.access_size.four i addr 0)
                   (CondNez i)
                   (SSeq (SOp s Syntax.bopname.add i i)
                         (SStore Syntax.access_size.four addr s 0)))).

    Definition compiled: list Instruction := Eval cbv in compile_stmt map.empty 0 0 doubler.
    Goal True.
      let c := eval cbv in compiled in pose c.
    Abort.
  End CompilationTest.

  Lemma load4bytes_in_MMIO_is_None: forall (m: mem) (addr: word),
      map.undef_on m isMMIOAddr ->
      isMMIOAddr addr ->
      Memory.load_bytes 4 m addr = None.
  Proof.
    intros. unfold Memory.load_bytes, map.undef_on, map.agree_on, map.getmany_of_tuple in *.
    simpl.
    rewrite H by assumption.
    rewrite map.get_empty.
    reflexivity.
  Qed.

  Lemma loadWord_in_MMIO_is_None: forall (m: mem) (addr: word),
      map.undef_on m isMMIOAddr ->
      isMMIOAddr addr ->
      Memory.loadWord m addr = None.
  Proof.
    intros. unfold Memory.loadWord.
    apply load4bytes_in_MMIO_is_None; assumption.
  Qed.

  Lemma storeWord_in_MMIO_is_None: forall (m: mem) (addr: word) v,
      map.undef_on m isMMIOAddr ->
      isMMIOAddr addr ->
      Memory.storeWord m addr v = None.
  Proof.
    unfold Memory.storeWord. intros. unfold Memory.store_bytes.
    rewrite load4bytes_in_MMIO_is_None; auto.
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
    unfold isMMIOAddr, IncrementWaitMMIOSpec in *.
    intros *. rewrite <-Forall_Exists_neg. intros.
    cbv [reg_addrs] in *.
    repeat lazymatch goal with
           | H : Exists _ (_ :: _) |- _ => inversion H; clear H; subst
           | H : Exists _ [] |- _ => solve [inversion H]
           | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
           | H : Forall _ [] |- _ => clear H
           end.
    all:congruence.
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
    change (@Utility.word Words32) with (@word p) in *;
    change (@parameters.word semantics_params) with (@word p) in *.

  Lemma reg_addrs_complete r : In (reg_addr r) reg_addrs.
  Proof. destruct r; cbn; tauto. Qed.
  Lemma reg_addr_is_mmio r : isMMIOAddr (reg_addr r).
  Proof.
    pose proof word.unsigned_range (reg_addr r).
    pose proof addrs_small as Hsmall.
    rewrite Forall_forall in Hsmall.
    specialize (Hsmall _ (reg_addrs_complete r)).
    cbv [isMMIOAddr IncrementWaitMMIOSpec].
    apply Exists_exists. exists (reg_addr r).
    split; [ apply reg_addrs_complete | ].
    simpl_paramrecords.
    auto with zarith.
  Qed.
  Lemma reg_addr_is_aligned r : word.unsigned (reg_addr r) mod 4 = 0.
  Proof.
    pose proof addrs_aligned as Halign.
    rewrite Forall_forall in Halign.
    apply Halign, reg_addrs_complete.
  Qed.

  Lemma compile_ext_call_correct: forall resvars extcall argvars,
      FlatToRiscvCommon.compiles_FlatToRiscv_correctly
        (@FlatToRiscvDef.compile_ext_call compilation_params)
        (FlatImp.SInteract resvars extcall argvars).
  Proof.
    unfold FlatToRiscvCommon.compiles_FlatToRiscv_correctly.
    simpl. intros.
    destruct H5 as [V_resvars V_argvars].
    rename extcall into action.
    pose proof (compile_ext_call_emits_valid FlatToRiscvDef.iset _ action _ V_resvars V_argvars).
    simp.
    destruct_RiscvMachine initialL.
    unfold compile_ext_call, FlatToRiscvCommon.goodMachine in *.
    match goal with
    | H: forall _ _, outcome _ _ -> _ |- _ => specialize H with (mReceive := map.empty)
    end.
    destruct (String.eqb action WRITE) eqn: E;
      cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics getXAddrs] in *.
    + (* MMOutput *)
      progress simpl in *|-.
      match goal with
      | H: IncrementWaitSemantics.ext_spec _ _ _ _ _ |- _ => rename H into Ex
      end.
      cbv [FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec ] in Ex.
      cbv [ext_spec FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec
                    IncrementWaitSemantics.ext_spec] in Ex.
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
      cbn in *|-.
      match goal with
      | H: map.split _ _ map.empty |- _ => rewrite map.split_empty_r in H; subst
      end.
      match goal with
      | HO : forall _ _ :  state, _ |- _ =>
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
      cbn in *.
      simp.
      eapply runsToNonDet.runsToStep_cps.
      split; simpl_MetricRiscvMachine_get_set. {
        intros _.
        eapply ptsto_instr_subset_to_isXAddr4.
        eapply shrink_footpr_subset. 1: eassumption.
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
      rewrite Z.mod_small by eapply EncodeBound.encode_range.
      rewrite DecodeEncode.decode_encode; cycle 1. {
        unfold valid_instructions in *. cbn in *. eauto.
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

      cbv [Utility.add Utility.ZToReg MachineWidth_XLEN]; rewrite add_0_r.
      unshelve erewrite (_ : _ = None); [eapply storeWord_in_MMIO_is_None; eauto using reg_addr_is_mmio|].

      cbv [MinimalMMIO.nonmem_store IncrementWaitMMIOSpec].
      split; [eauto using reg_addr_is_mmio|].
      split; [red; auto using reg_addr_is_aligned|].

      repeat fwd.

      eapply runsToNonDet.runsToDone.
      simpl_MetricRiscvMachine_get_set.
      simpl_word_exprs word_ok.
      unfold mmioStoreEvent, signedByteTupleToReg in *.
      unfold regToInt32.
      rewrite LittleEndian.combine_split.
      rewrite sextend_width_nop by reflexivity.
      rewrite Z.mod_small by apply word.unsigned_range.
      rewrite word.of_Z_unsigned.
      apply eqb_eq in E. subst action.
      cbn -[invalidateWrittenXAddrs] in *.
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
        clear -(*D4 M0*) D consts_ok circuit_spec.
        unfold invalidateWrittenXAddrs.
        change removeXAddr with (@List.removeb word word.eqb _).
        rewrite ?ListSet.of_list_removeb.
        unfold map.undef_on, map.agree_on, disjoint in *.
        unfold subset, diff, singleton_set, of_list, PropSet.elem_of in *.
        intros y HIn.
        specialize (D y). destruct D; [contradiction|].
        rewrite ?and_assoc.
        split; [exact HIn|clear HIn].
        pose proof addrs_small (constants_ok:=consts_ok) as Hsmall.
        rewrite Forall_forall in Hsmall. specialize (Hsmall _ (reg_addrs_complete x)).
        pose proof (word.unsigned_range (reg_addr x)).
        ssplit; eapply disjoint_MMIO_goal; eauto.
        all:cbv [isMMIOAddr IncrementWaitMMIOSpec].
        all:eapply Exists_exists; exists (reg_addr x).
        all:split; [ apply reg_addrs_complete | ].
        all:simpl_paramrecords.
        all:push_unsigned.
        all:auto with zarith. }
      ssplit; eauto.
      unfold invalidateWrittenXAddrs.
      change removeXAddr with (@List.removeb word word.eqb _).
      rewrite ?ListSet.of_list_removeb.
      repeat apply disjoint_diff_l.
      assumption.

    + (* MMInput *)
      simpl in *|-.
      match goal with
      | H: IncrementWaitSemantics.ext_spec _ _ _ _ _ |- _ => rename H into Ex
      end.
      cbv [FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec ] in Ex.
      cbv [ext_spec FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec
                    IncrementWaitSemantics.ext_spec] in Ex.
      simpl in *|-.

      rewrite E in *.
      destruct (action =? READ)%string eqn:EE in Ex; try contradiction.
      logical_simplify; subst.
      repeat match goal with
             | l: list _ |- _ => destruct l;
                                 try (exfalso; (contrad || (cheap_saturate; contrad))); []
             end.
      destruct argvars; cycle 1. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn in *; simp; destruct_one_match_hyp; congruence
        end.
      }
      cbn in *|-.
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
      cbn in *.
      eapply runsToNonDet.runsToStep_cps.
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
      unshelve erewrite (_ : _ = None); [eapply loadWord_in_MMIO_is_None|]; eauto using reg_addr_is_mmio.

      cbv [MinimalMMIO.nonmem_load IncrementWaitMMIOSpec].
      split; [apply reg_addr_is_mmio|].
      split; [red; auto using reg_addr_is_aligned|].
      split.
      { cbv [MMIOReadOK].
        let val := lazymatch goal with
                   | H : read_step _ _ ?val _ |- _ => val end in
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
      | H : reg_addr _ = reg_addr _ |- _ =>
        apply reg_addrs_unique in H; subst
      end.
      lazymatch goal with
      | HO : forall _ _ v, _ -> read_step _ _ v _ -> _ |- _ =>
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
Existing Instance semantics_params.
Existing Instance compilation_params.
Existing Instance FlatToRiscv_params.
Existing Instance FlatToRiscv_hyps.
