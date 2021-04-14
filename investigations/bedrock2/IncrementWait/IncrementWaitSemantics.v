Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.DecimalString.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList.
Require coqutil.Map.SortedListString coqutil.Map.SortedListWord.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Z.HexNotation.
Require Import coqutil.Decidable.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Loosely based on bedrock2/FE310CSemantics.v *)

Definition unique_words
           {width} {word: word.word width} {word_ok:word.ok word}
           (l : list word.rep) : Prop :=
  List.dedup word.eqb l = l.

Module constants.
  Class constants T :=
    { VALUE_ADDR : T;
      STATUS_ADDR : T;
      STATUS_IDLE : T;
      STATUS_BUSY : T;
      STATUS_DONE : T }.

  Definition constant_vars
           {names : constants string}
    : constants expr :=
    {| VALUE_ADDR := expr.var VALUE_ADDR;
       STATUS_ADDR := expr.var STATUS_ADDR;
       STATUS_IDLE := expr.var STATUS_IDLE;
       STATUS_BUSY := expr.var STATUS_BUSY;
       STATUS_DONE := expr.var STATUS_DONE |}.

  Definition constant_names : constants string :=
    {| VALUE_ADDR := "VALUE_ADDR";
       STATUS_ADDR := "STATUS_ADDR";
       STATUS_IDLE := "STATUS_IDLE";
       STATUS_BUSY := "STATUS_BUSY";
       STATUS_DONE := "STATUS_DONE" |}.

  Definition globals {T} {consts : constants T} : list T :=
    [VALUE_ADDR; STATUS_ADDR; STATUS_IDLE; STATUS_BUSY; STATUS_DONE].

  Class ok
        {word : word.word 32} {word_ok : word.ok word}
        (global_values : constants word.rep) :=
    { addrs_unique : VALUE_ADDR <> STATUS_ADDR;
      flags_unique_and_nonzero :
        unique_words
          ((word.of_Z 0)
             :: (map (fun flag_position => word.slu (word.of_Z 1) flag_position)
                    [STATUS_IDLE; STATUS_BUSY; STATUS_DONE]));
    }.
End constants.
Notation constants := constants.constants.

(* Circuit timing properties *)
Module timing.
  Class timing := { ncycles_processing : nat }.
End timing.
Notation timing := timing.timing.

Module parameters.
  Class parameters :=
    { word :> Interface.word.word 32;
      mem :> Interface.map.map word.rep Byte.byte;
    }.

  Class ok (p : parameters) :=
    { word_ok :> word.ok word; (* for impl of mem below *)
      mem_ok :> Interface.map.ok mem; (* for impl of mem below *)
    }.
End parameters.
Notation parameters := parameters.parameters.

Definition READ := "REG32_GET".
Definition WRITE := "REG32_SET".

Section WithParameters.
  Context {p : parameters} {p_ok : parameters.ok p}.
  Context {consts : constants word.rep} {timing : timing}.
  Import constants parameters.

  Local Notation bedrock2_event := (mem * string * list word * (mem * list word))%type.
  Local Notation bedrock2_trace := (list bedrock2_event).

  Inductive Register := VALUE | STATUS.

  (* state *from the perspective of the software* *)
  Inductive state :=
  | IDLE
  | BUSY (input : word) (max_cycles_until_done : nat)
  | DONE (answer : word)
  .

  Inductive reg_addr : Register -> word -> Prop :=
  | addr_value : reg_addr VALUE VALUE_ADDR
  | addr_status : reg_addr STATUS STATUS_ADDR
  .

  Definition status_flag (s : state) : word :=
    match s with
    | IDLE => STATUS_IDLE
    | BUSY _ _ => STATUS_BUSY
    | DONE _ => STATUS_DONE
    end.

  Definition status_value (flag : word) : word :=
    word.slu (word.of_Z 1) flag.

  (* circuit spec *)
  Definition proc : word -> word := word.add (word.of_Z 1).

  Inductive read_step : state -> Register -> word -> state -> Prop :=
  | ReadStatusStayIdle :
      forall val,
        val = status_value STATUS_IDLE ->
        read_step IDLE STATUS val IDLE
  | ReadStatusStayBusy :
      forall val input n,
        val = status_value STATUS_BUSY ->
        (* Since a read takes one cycle, the maximum number of cycles before the
           status is DONE decreases by one *)
        read_step (BUSY input (S n)) STATUS val (BUSY input n)
  | ReadStatusStayDone :
      forall val answer,
        val = status_value STATUS_DONE ->
        read_step (DONE answer) STATUS val (DONE answer)
  | ReadStatusFinish :
      forall input val n,
        val = status_value STATUS_DONE ->
        read_step (BUSY input n) STATUS val (DONE (proc input))
  | ReadOutput :
      forall val,
        read_step (DONE val) VALUE val IDLE
  .

  Inductive write_step : state -> Register -> word -> state -> Prop :=
  | WriteInput :
      forall val,
        write_step IDLE VALUE val (BUSY val timing.ncycles_processing)
  .

  Inductive step : string -> state -> list word -> list word -> state -> Prop :=
  | ReadStep :
      forall s s' r addr val,
        reg_addr r addr ->
        read_step s r val s' ->
        step READ s [addr] [val] s'
  | WriteStep :
      forall s s' r addr val,
        reg_addr r addr ->
        write_step s r val s' ->
        step WRITE s [addr;val] [] s'
  .

  (* Computes the Prop that must hold for this state to be accurate after the
     trace *)
  Fixpoint execution (t : bedrock2_trace) (s : state) : Prop :=
    match t with
    | [] => s = IDLE
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
    Semantics.width := 32;
    Semantics.word := parameters.word;
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
    { cbv; auto. }
    { exact (SortedListString.ok _). }
    { exact (SortedListString.ok _). }
  Qed.

  (* COPY-PASTE this *)
  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
End WithParameters.
