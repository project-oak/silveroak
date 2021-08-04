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
Require Import Bedrock2Experiments.ProgramSemantics32.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.WhileProperties.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.LibBase.Bitfield.
Require Import coqutil.Map.SortedListString.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Section Proof.
  Context {word: word.word 32} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}
          {ext_spec: ExtSpec} {ext_spec_ok: ext_spec.ok ext_spec}.

  Global Instance spec_of_bitfield_field32_read : spec_of "b2_bitfield_field32_read" :=
    fun function_env =>
      forall (field mask index : word) (m : mem) (t : trace),
        call function_env bitfield_field32_read t m [field; mask; index]
          (fun t' m' rets =>
          t = t' /\ m = m' /\ rets = [select_bits field index mask]
          ).

  Lemma bitfield_field32_read_correct :
    program_logic_goal_for_function! bitfield_field32_read.
  Proof.
    repeat straightline.
    repeat split; try reflexivity.
  Qed.

  Global Instance spec_of_bitfield_bit32_read : spec_of "b2_bitfield_bit32_read" :=
    fun function_env =>
      forall (field : word) (index: word) (m : mem) (t : trace),
        call function_env bitfield_bit32_read t m [field; index]
          (fun t' m' rets =>
          t = t' /\ m = m' /\
          rets = [word.and (word.sru field index) (word.of_Z 1)]
          ).

  Lemma bitfield_bit32_read_correct :
    program_logic_goal_for_function! bitfield_bit32_read.
  Proof.
    repeat straightline.
    (* call bitfield_field32_read *)
    straightline_call; eauto; try reflexivity; [ ].
    unfold select_bits in *.
    repeat straightline.
    repeat split; try reflexivity.
  Qed.
End Proof.
