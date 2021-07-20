Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.TailRecursion.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.letexists.
Require Import coqutil.Z.Lia.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.WhileProperties.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import coqutil.Map.SortedListString.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.


Section Proof.
  Import parameters.
  Context {width word mem} {p : StateMachineSemantics.parameters width word mem}.
  Context (p_ok : StateMachineSemantics.parameters.ok p).

  Global Instance spec_of_abs_mmio_read32 : spec_of "abs_mmio_read32" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (s : state) (addr : word) r,
        StateMachineSemantics.parameters.reg_addr r = addr ->
        (exists val s', parameters.read_step 4 s r val s') ->
        execution tr s ->
        call function_env abs_mmio_read32 tr m [addr]
        (fun tr' m' rets =>
          exists s' val,
          rets = [val]
          /\ tr' = ((map.empty, MMIOLabels.READ32, [addr], (map.empty, [val])) :: tr)
          /\ execution tr' s'
          /\ m = m'
        ).
  Lemma abs_mmio_read32_correct :
    program_logic_goal_for_function! abs_mmio_read32.
  Proof.
    repeat straightline.
    eapply (interact_read 4); repeat straightline; eauto.
    - rewrite <- H. reflexivity.
    - do 3 eexists; ssplit; eauto.
      cbv [parameters.read_step ] in *.
      rewrite <- H. reflexivity.
  Qed.

End Proof.
