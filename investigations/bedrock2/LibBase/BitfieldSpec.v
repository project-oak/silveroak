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
Require Import Bedrock2Experiments.LibBase.Bitfield.

Require Import coqutil.Map.SortedListString.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Class parameters :=
  { word :> Interface.word.word 32;
    mem :> Interface.map.map word Byte.byte;
    ext_spec : list
    (mem * string * list word *
    (mem * list word)) ->
    mem ->
    string ->
    list word ->
    (mem -> list word -> Prop) -> Prop
  }.

Instance semantics_parameters {p : parameters}: Semantics.parameters :=
{|
  Semantics.width := 32;
  Semantics.word := word;
  Semantics.mem := mem;
  Semantics.locals := SortedListString.map _;
  Semantics.env := SortedListString.map _;
  Semantics.ext_spec := ext_spec;
|}.

Class ok (p : parameters) :=
  {  word_ok :> word.ok word;
    mem_ok :> Interface.map.ok mem;
    ext_spec_ok :> ext_spec.ok semantics_parameters;
  }.

Instance semantics_parameters_ok {p : parameters} {ok : ok p}: Semantics.parameters_ok semantics_parameters.
Proof.
  split.
  - cbv. left. reflexivity.
  - exact word_ok.
  - exact mem_ok.
  - exact (SortedListString.ok _).
  - exact (SortedListString.ok _).
  - exact ext_spec_ok.
Qed.

Section Proof.
  Context {p : parameters} {p_ok : ok p}.

  Instance spec_of_bitfield_field32_write : spec_of "b2_bitfield_field32_write" :=
    fun function_env =>
      forall (field mask index value : word) (R : mem -> Prop) (m : mem) (t : trace),
        call function_env bitfield_field32_write t m [field; mask; index; value]
          (fun t' m' rets =>
          t = t' /\ m = m' /\ exists v, rets = [v]
          /\ value = (select_bits v index mask)).
  Lemma bitfield_field32_write_correct :
    program_logic_goal_for_function! bitfield_field32_write.
  Proof.
    repeat straightline.
    repeat split; try reflexivity.
    cbv [bitfield0] in *.
    Search word.or.
    exists bitfield.
    repeat split; try reflexivity.
    Admitted.

  Instance spec_of_bitfield_field32_read : spec_of "b2_bitfield_field32_read" :=
    fun function_env =>
      forall (field mask index : word) (R : mem -> Prop) (m : mem) (t : trace),
        call function_env bitfield_field32_read t m [field; mask; index]
          (fun t' m' rets =>
          t = t' /\ m = m' /\ exists v, rets = [v] /\
          v = select_bits field index mask
          ).

  Lemma bitfield_field32_read_correct :
    program_logic_goal_for_function! bitfield_field32_read.
  Proof.
    repeat straightline.
    repeat split; try reflexivity.
    exists out.
    repeat split; try reflexivity.
  Qed.

  Instance spec_of_bitfield_bit32_read : spec_of "b2_bitfield_bit32_read" :=
    fun function_env =>
      forall (field : word) (index: word) (R : mem -> Prop) (m : mem) (t : trace),
        call function_env bitfield_bit32_read t m [field; index]
          (fun t' m' rets =>
          t = t' /\ m = m' /\ exists v, rets = [v] /\
          v = (word.and (word.sru field index) (word.of_Z 1))
          ).

  Lemma bitfield_bit32_read_correct :
    program_logic_goal_for_function! bitfield_bit32_read.
  Proof.
    repeat straightline.

    (* call bitfield_field32_read *)
    straightline_call; eauto; try reflexivity; [ ].

    repeat straightline.
    repeat split; try reflexivity.
    exists x.
    repeat split; try reflexivity.
  Qed.

End Proof.
