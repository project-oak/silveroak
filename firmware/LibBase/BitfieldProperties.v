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

  Global Instance spec_of_bitfield_field32_write : spec_of "b2_bitfield_field32_write" :=
    fun function_env =>
      forall (field mask index value : word) (m : mem) (t : trace),
        call function_env bitfield_field32_write t m [field; mask; index; value]
          (fun t' m' rets =>
            t = t' /\ m = m' /\
            rets = [word.or
              (word.and
                field
                (word.xor (word.slu mask index) (word.of_Z (- 1)))
              )
              (word.slu (word.and value mask) index)]).
  Lemma bitfield_field32_write_correct :
    program_logic_goal_for_function! bitfield_field32_write.
  Proof.
    repeat straightline.
    repeat lazymatch goal with
           | |- exists _, _ =>
             eexists; ssplit; repeat straightline
    end.
    ssplit; eauto.
  Qed.

  Global Instance spec_of_bitfield_bit32_write : spec_of "b2_bitfield_bit32_write" :=
  fun function_env =>
    forall (field index value: word) (m : mem) (t : trace),
      call function_env bitfield_bit32_write t m [field; index; value]
        (fun t' m' rets =>
           t = t' /\ m = m' /\
           rets = [word.or
              (word.and
                field
                (word.xor (word.slu (word.of_Z 1) index) (word.of_Z (- 1)))
              )
              (word.slu (word.and (if word.eqb value (word.of_Z 1) then word.of_Z 1 else word.of_Z 0) (word.of_Z 1)) index)]).
  Lemma bitfield_bit32_write_correct :
    program_logic_goal_for_function! bitfield_bit32_write.
  Proof.
    repeat straightline.
    straightline_call.
    eexists; ssplit; repeat straightline.
    + cbn [map.putmany_of_list_zip]. subst a1.
      reflexivity.
    + repeat straightline. ssplit; eauto.
  Qed.

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
