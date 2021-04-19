Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList.
Require coqutil.Map.SortedListString coqutil.Map.SortedListWord.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Loosely based on bedrock2/FE310CSemantics.v *)

Module parameters.
  Class parameters {width} {word : Interface.word.word width} :=
    { state : Type;
      register : Type;
      mem : Interface.map.map word.rep Byte.byte;
      READ : string;
      WRITE : string;
      initial_state : state;
      read_step : state -> register -> word -> state -> Prop;
      write_step : state -> register -> word -> state -> Prop;
      reg_addr : register -> word;
    }.
  Global Arguments parameters : clear implicits.

  Class ok {width word} (p : parameters width word) :=
    { width_ok : width = 32 \/ width = 64;
      word_ok : word.ok word; (* for impl of mem below *)
      mem_ok : Interface.map.ok mem; (* for impl of mem below *)
    }.
End parameters.
Notation parameters := parameters.parameters.

Section WithParameters.
  Import parameters.
  Context {width word} {p : parameters width word}
          {p_ok : parameters.ok p}.

  Local Notation bedrock2_event := (mem * string * list word * (mem * list word))%type.
  Local Notation bedrock2_trace := (list bedrock2_event).

  Inductive step : string -> state -> list word -> list word -> state -> Prop :=
  | ReadStep :
      forall (s s' : state) r addr val,
        reg_addr r = addr ->
        read_step s r val s' ->
        step READ s [addr] [val] s'
  | WriteStep :
      forall s s' r addr val,
        reg_addr r = addr ->
        write_step s r val s' ->
        step WRITE s [addr;val] [] s'
  .

  (* Computes the Prop that must hold for this state to be accurate after the
     trace *)
  Fixpoint execution (t : bedrock2_trace) (s : state) : Prop :=
    match t with
    | [] => s = initial_state
    | (_,action,args,(_,rets)) :: t =>
      exists prev_state,
      execution t prev_state
      /\ step action prev_state args rets s
    end.

  Definition ext_spec (t : bedrock2_trace)
             (mGive : mem)
             (action : string)
             (args: list word)
             (post: mem -> list word -> Prop) :=
    (* no memory ever given away *)
    mGive = Interface.map.empty
    /\ forall st rets,
      execution ((map.empty,action,args,(map.empty,rets)) :: t) st ->
      post Interface.map.empty rets.

  Global Instance semantics_parameters  : Semantics.parameters :=
    {|
    Semantics.width := width;
    Semantics.word := word;
    Semantics.mem := parameters.mem;
    Semantics.locals := SortedListString.map _;
    Semantics.env := SortedListString.map _;
    Semantics.ext_spec := ext_spec;
  |}.

  Global Instance ext_spec_ok : ext_spec.ok _.
  Proof.
    constructor.
    all:cbv [ext_spec Semantics.ext_spec semantics_parameters].
    all:cbv [Morphisms.pointwise_relation Basics.impl].
    all:cbn [execution].
    all:repeat intro.
    all:repeat lazymatch goal with
               | H: _ /\ _ |- _ => destruct H
               | H: exists _, _ |- _ => destruct H
               | |- map.same_domain ?x ?x => apply Properties.map.same_domain_refl
               |  |- ?x = ?x /\ _ => split; [ reflexivity | ]
               | _ => progress subst
               end.
    all:eauto.
  Qed.

  Global Instance ok : Semantics.parameters_ok semantics_parameters.
  Proof.
    split; cbv [env locals mem semantics_parameters]; try exact _.
    { exact width_ok. }
    { exact word_ok. }
    { exact mem_ok. }
    { exact (SortedListString.ok _). }
    { exact (SortedListString.ok _). }
  Defined.

  (* COPY-PASTE this *)
  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
End WithParameters.
