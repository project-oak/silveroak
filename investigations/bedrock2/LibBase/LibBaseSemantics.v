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

Global Instance semantics_parameters {p : parameters}: Semantics.parameters :=
{|
  Semantics.width := 32;
  Semantics.word := word;
  Semantics.mem := mem;
  Semantics.locals := SortedListString.map _;
  Semantics.env := SortedListString.map _;
  Semantics.ext_spec := ext_spec;
|}.

Class parameters_ok (p : parameters) :=
  {  word_ok :> word.ok word;
    mem_ok :> Interface.map.ok mem;
    ext_spec_ok :> ext_spec.ok semantics_parameters;
  }.

Global Instance semantics_parameters_ok {p : parameters} {ok : parameters_ok p}:
Semantics.parameters_ok semantics_parameters.
Proof.
  split.
  - cbv. left. reflexivity.
  - exact word_ok.
  - exact mem_ok.
  - exact (SortedListString.ok _).
  - exact (SortedListString.ok _).
  - exact ext_spec_ok.
Qed.

