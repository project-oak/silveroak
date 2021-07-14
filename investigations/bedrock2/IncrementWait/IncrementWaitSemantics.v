Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.DecimalString.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.ZnWords.
Require coqutil.Datatypes.String coqutil.Map.SortedList.
Require coqutil.Map.SortedListString coqutil.Map.SortedListWord.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.HexNotation.
Require Import coqutil.Decidable.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.StateMachineSemantics.
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
  Context {circuit_spec : circuit_behavior}.
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
    | VALUE => word.of_Z VALUE_ADDR
    | STATUS => word.of_Z STATUS_ADDR
    end.

  Lemma reg_addrs_unique r1 r2 : reg_addr r1 = reg_addr r2 -> r1 = r2.
  Proof.
    destruct r1, r2; cbv [reg_addr]; intros; try reflexivity;
      exfalso; unfold VALUE_ADDR, STATUS_ADDR, INCR_BASE_ADDR in *; ZnWords.
  Qed.

  Definition status_flag (s : state) : word :=
    match s with
    | IDLE => word.of_Z STATUS_IDLE
    | BUSY _ _ => word.of_Z STATUS_BUSY
    | DONE _ => word.of_Z STATUS_DONE
    end.

  Definition status_value (flag : Z) : word :=
    word.slu (word.of_Z 1) (word.of_Z flag).

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

  Global Instance state_machine_parameters
    : StateMachineSemantics.parameters 32 word mem :=
    {| StateMachineSemantics.parameters.state := state ;
       StateMachineSemantics.parameters.register := Register ;
       StateMachineSemantics.parameters.is_initial_state := eq IDLE ;
       StateMachineSemantics.parameters.read_step sz s a v s' :=
         sz = 4%nat /\ read_step s a v s';
       StateMachineSemantics.parameters.write_step sz s a v s' :=
         sz = 4%nat /\ write_step s a v s' ;
       StateMachineSemantics.parameters.reg_addr := reg_addr ;
       StateMachineSemantics.parameters.isMMIOAddr a :=
           INCR_BASE_ADDR <= word.unsigned a < INCR_END_ADDR;
    |}.

  Global Instance state_machine_parameters_ok
    : StateMachineSemantics.parameters.ok state_machine_parameters.
  Proof.
    constructor;
      unfold parameters.isMMIOAddr; cbn;
      intros;
      try exact _;
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | r: Register |- _ =>
               destruct r; cbn [reg_addr] in *; unfold VALUE_ADDR, STATUS_ADDR, INCR_BASE_ADDR in *
             end;
      subst;
      eauto.
    all: try ZnWords.
    all: exfalso; ZnWords.
  Qed.

  (* COPY-PASTE this *)
  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
End WithParameters.
