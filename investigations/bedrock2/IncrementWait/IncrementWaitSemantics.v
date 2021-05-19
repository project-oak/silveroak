Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.DecimalString.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList.
Require coqutil.Map.SortedListString coqutil.Map.SortedListWord.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.HexNotation.
Require Import coqutil.Decidable.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.IncrementWait.Constants.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Loosely based on bedrock2/FE310CSemantics.v *)

(* Circuit specification *)
Class circuit_behavior :=
  { ncycles_processing : nat
  }.

Module parameters.
  Class parameters :=
    { word :> Interface.word.word 32;
      mem :> Interface.map.map word Byte.byte;
    }.

  Class ok (p : parameters) :=
    { word_ok :> word.ok word; (* for impl of mem below *)
      mem_ok :> Interface.map.ok mem; (* for impl of mem below *)
    }.
End parameters.
Notation parameters := parameters.parameters.

Section WithParameters.
  Context {p : parameters} {p_ok : parameters.ok p}.
  Context {consts : constants word.rep} {consts_ok : constants_ok consts}
          {circuit_spec : circuit_behavior}.
  Import parameters.

  Local Notation bedrock2_event := (mem * string * list word * (mem * list word))%type.
  Local Notation bedrock2_trace := (list bedrock2_event).

  Inductive Register := VALUE | STATUS.

  (* state *from the perspective of the software* *)
  Inductive state :=
  | IDLE
  | BUSY (input : word) (max_cycles_until_done : nat)
  | DONE (answer : word)
  .

  Definition reg_addr (r : Register) : word :=
    match r with
    | VALUE => VALUE_ADDR
    | STATUS => STATUS_ADDR
    end.

  Lemma reg_addrs_unique r1 r2 : reg_addr r1 = reg_addr r2 -> r1 = r2.
  Proof.
    pose proof addrs_unique as Haddrs.
    cbv [reg_addrs] in Haddrs. simplify_unique_words_in Haddrs.
    destruct r1, r2; cbv [reg_addr]; congruence.
  Qed.

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

  Definition read_step (s : state) (r : Register) (val : word) (s' : state)
    : Prop :=
    match r with
    | STATUS =>
      match s with
      | IDLE => val = status_value STATUS_IDLE /\ s' = IDLE
      | DONE answer => val = status_value STATUS_DONE /\ s' = DONE answer
      | BUSY input n =>
        (* either the status is DONE and we transition to the DONE state *)
        (val = status_value STATUS_DONE /\ s' = DONE (proc input))
        (* ...or the status is BUSY and we stay in the BUSY state *)
        \/ (exists n', n = S n' /\ val = status_value STATUS_BUSY /\ s' = BUSY input n')
      end
    | VALUE =>
      match s with
      | DONE answer => val = answer /\ s' = IDLE
      | _ => False (* cannot read VALUE in any state other than DONE *)
      end
    end.

  Definition write_step (s : state) (r : Register) (val : word) (s' : state)
    : Prop :=
    match r with
    | STATUS => False (* not writeable *)
    | VALUE =>
      match s with
      | IDLE => s' = BUSY val ncycles_processing
      | _ => False (* cannot write VALUE in any state other than IDLE *)
      end
    end.

  Definition step
             (action : string) (s : state) (args rets : list word) (s' : state)
    : Prop :=
    if String.eqb action WRITE
    then match args with
         | [addr;val] =>
           (exists r, reg_addr r = addr /\ rets = [] /\ write_step s r val s')
         | _ => False
         end
    else if String.eqb action READ
         then match args with
              | [addr] => (exists r val, reg_addr r = addr /\ rets = [val] /\ read_step s r val s')
              | _ => False
              end
         else False.

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
    if String.eqb action WRITE
    then
      (exists r addr val,
          args = [addr;val]
          /\ mGive = map.empty
          /\ reg_addr r = addr
          (* there must exist *at least one* possible state given this trace,
             and one possible transition given these arguments *)
          /\ (exists s s', execution t s /\ write_step s r val s')
          (* postcondition must hold for *all* possible states/transitions *)
          /\ (forall s s',
                execution t s ->
                write_step s r val s' ->
                post Interface.map.empty []))
       else if String.eqb action READ
            then
              (exists r addr,
                  args = [addr]
                  /\ mGive = map.empty
                  /\ reg_addr r = addr
                  (* there must exist *at least one* possible state given this
                     trace, and one possible transition given these arguments *)
                  /\ (exists s s' val, execution t s /\ read_step s r val s')
                  (* postcondition must hold for *all* possible states/transitions *)
                  /\ (forall s s' val,
                        execution t s ->
                        read_step s r val s' ->
                        post Interface.map.empty [val]))
               else False.

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
    split;
    cbv [ext_spec Semantics.ext_spec semantics_parameters
    Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl
    ];
    intros.
    all :
    repeat match goal with
           | H : context[(?x =? ?y)%string] |- _ =>
             destruct (x =? y)%string in *
           | H: exists _, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           | H : _ :: _  = _ :: _ |- _ => inversion H; clear H; subst
           | H: False |- _ => destruct H
           | H : reg_addr _ = reg_addr _ |- _ => apply reg_addrs_unique in H
           | _ => progress subst
           end; eauto 20 using Properties.map.same_domain_refl.
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
