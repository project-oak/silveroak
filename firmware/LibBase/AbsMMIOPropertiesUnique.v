Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Bedrock2Experiments.ProgramSemantics32.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.

Section Proof.
  Context {word: word.word 32} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}
          {M: state_machine.parameters}.
  (* Note that these two will have to be provided at proof linking time, not at straightline_call *)
  Context {M_ok: state_machine.ok M}
          (execution_unique: forall t s1 s2, execution t s1 -> execution t s2 -> s1 = s2).

  Global Instance spec_of_abs_mmio_write8 : spec_of "abs_mmio_write8" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (s : M) (s' : M) (addr : word) (value : word) r,
        state_machine.reg_addr r = addr ->
        state_machine.write_step 1 s r value s' ->
        execution tr s ->
        call function_env abs_mmio_write8 tr m [addr; value]
        (fun tr' m' rets =>
          rets = []
          /\ tr' = ((map.empty, MMIOLabels.WRITE8, [addr; value], (map.empty, [])) :: tr)
          /\ execution tr' s'
          /\ m = m'
        ).
  Lemma abs_mmio_write8_correct :
    program_logic_goal_for_function! abs_mmio_write8.
  Proof.
    repeat straightline.
    eapply (interact_write 1); repeat straightline.
    - rewrite <- H. reflexivity.
    - do 2 eexists; ssplit; eauto.
    - rewrite <- H; ssplit; eauto.
      match goal with
      | H: execution ?t ?s1 |- execution ?t ?s2 =>
        replace s2 with s1;
        [exact H | eapply execution_unique]
      end.
      all: eapply execution_step_write; [..|eassumption]; eauto.
  Qed.

  Global Instance spec_of_abs_mmio_write32 : spec_of "abs_mmio_write32" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (s : M) (s' : M) (addr : word) (value : word) r,
        state_machine.reg_addr r = addr ->
        state_machine.write_step 4 s r value s' ->
        execution tr s ->
        call function_env abs_mmio_write32 tr m [addr; value]
        (fun tr' m' rets =>
          rets = []
          /\ tr' = ((map.empty, MMIOLabels.WRITE32, [addr; value], (map.empty, [])) :: tr)
          /\ execution tr' s'
          /\ m = m'
        ).
  Lemma abs_mmio_write32_correct :
    program_logic_goal_for_function! abs_mmio_write32.
  Proof.
    repeat straightline.
    eapply (interact_write 4); repeat straightline.
    - rewrite <- H. reflexivity.
    - do 2 eexists; ssplit; eauto.
    - rewrite <- H; ssplit; eauto.
      match goal with
      | H: execution ?t ?s1 |- execution ?t ?s2 =>
        replace s2 with s1;
        [exact H | eapply execution_unique]
      end.
      all: eapply execution_step_write; [..|eassumption]; eauto.
  Qed.

  Global Instance spec_of_abs_mmio_read8 : spec_of "abs_mmio_read8" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (s : M) (addr : word) r val s',
        state_machine.reg_addr r = addr ->
        state_machine.read_step 1 s r val s' ->
        execution tr s ->
        call function_env abs_mmio_read8 tr m [addr]
        (fun tr' m' rets =>
          exists s' val,
          rets = [val]
          /\ tr' = ((map.empty, MMIOLabels.READ8, [addr], (map.empty, [val])) :: tr)
          /\ state_machine.read_step 1 s r val s' (* <-- redundant, but convenient *)
          /\ execution tr' s'
          /\ m = m'
        ).
  Lemma abs_mmio_read8_correct :
    program_logic_goal_for_function! abs_mmio_read8.
  Proof.
    repeat straightline.
    eapply (interact_read 1); repeat straightline; eauto.
    - rewrite <- H. reflexivity.
    - match goal with
      | H1: execution ?t ?s1, H2: execution ?t ?s2 |- _ =>
        pose proof (execution_unique _ _ _ H1 H2);
        subst s2;
        clear H2
      end.
      do 3 eexists; ssplit; eauto.
      rewrite <- H. reflexivity.
  Qed.

  Global Instance spec_of_abs_mmio_read32 : spec_of "abs_mmio_read32" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (s : M) (addr : word) r val s',
        state_machine.reg_addr r = addr ->
        state_machine.read_step 4 s r val s' ->
        execution tr s ->
        call function_env abs_mmio_read32 tr m [addr]
        (fun tr' m' rets =>
          exists s' val,
          rets = [val]
          /\ tr' = ((map.empty, MMIOLabels.READ32, [addr], (map.empty, [val])) :: tr)
          /\ state_machine.read_step 4 s r val s' (* <-- redundant, but convenient *)
          /\ execution tr' s'
          /\ m = m'
        ).
  Lemma abs_mmio_read32_correct :
    program_logic_goal_for_function! abs_mmio_read32.
  Proof.
    repeat straightline.
    eapply (interact_read 4); repeat straightline; eauto.
    - rewrite <- H. reflexivity.
    - match goal with
      | H1: execution ?t ?s1, H2: execution ?t ?s2 |- _ =>
        pose proof (execution_unique _ _ _ H1 H2);
        subst s2;
        clear H2
      end.
      do 3 eexists; ssplit; eauto.
      rewrite <- H. reflexivity.
  Qed.

End Proof.
