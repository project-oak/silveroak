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
Require Import Bedrock2Experiments.LibBase.LibBaseSemantics.
Require Import coqutil.Map.SortedListString.

Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Section Proof.
  Import LibBaseSemantics.
  Context {p : parameters} {p_ok : parameters_ok p}.

  Instance spec_of_abs_mmio_read32 : spec_of "abs_mmio_read32" :=
    fun function_env =>
      forall (addr : word) (R : mem -> Prop) (m : mem) (t : trace),
        call function_env abs_mmio_read32 t m [addr]
        (fun t' m' rets => t = t' /\ m = m').

  Check ( _ : spec_of abs_mmio_read32).
  Lemma abs_mmio_read32_correct :
    program_logic_goal_for_function! abs_mmio_read32.
  Proof.
  Admitted.

End Proof.
