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
          {M: state_machine.parameters} {M_ok: state_machine.ok M}.

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
          /\ (exists s'', execution tr' s'')
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
          /\ (exists s'', execution tr' s'')
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
  Qed.

End Proof.
