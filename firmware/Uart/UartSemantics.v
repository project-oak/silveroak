Require Import Coq.ZArith.ZArith.
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
Require Import Bedrock2Experiments.Uart.Constants.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.List.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Circuit specification *)
Class circuit_behavior :=
  { ncycles_processing : nat
  }.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {circuit_spec : circuit_behavior}.

  Add Ring wring : (Properties.word.ring_theory (word := word))
    (preprocess [autorewrite with rew_word_morphism],
    morphism (Properties.word.ring_morph (word := word)),
    constants [Properties.word_cst]).

  Inductive Register : Set :=
  | INTR_STATE
  | INTR_ENABLE
  | INTR_TEST
  | CTRL
  | STATUS
  | RDATA
  | WDATA
  | FIFO_CTRL
  | FIFO_STATUS
  | OVRD
  | VAL
  | TIMEOUT_CTRL
  .

  Definition all_regs : list Register :=
    [ INTR_STATE ; INTR_ENABLE ; INTR_TEST
      ; CTRL ; STATUS ; RDATA ; WDATA ; FIFO_CTRL ; FIFO_STATUS
      ; OVRD ; VAL ; TIMEOUT_CTRL ].

  Lemma all_regs_complete r : In r all_regs.
  Proof. cbv [all_regs In]. destruct r; tauto. Qed.

  Definition reg_addr (r : Register) : word :=
    let base := TOP_EARLGREY_UART0_BASE_ADDR in
    match r with
    | INTR_STATE => word.of_Z (base + UART_INTR_STATE_REG_OFFSET)
    | INTR_ENABLE => word.of_Z (base + UART_INTR_ENABLE_REG_OFFSET)
    | INTR_TEST => word.of_Z (base + UART_INTR_TEST_REG_OFFSET)
    | CTRL => word.of_Z (base + UART_CTRL_REG_OFFSET)
    | STATUS => word.of_Z (base + UART_STATUS_REG_OFFSET)
    | RDATA => word.of_Z (base + UART_RDATA_REG_OFFSET)
    | WDATA => word.of_Z (base + UART_WDATA_REG_OFFSET)
    | FIFO_CTRL => word.of_Z (base + UART_FIFO_CTRL_REG_OFFSET)
    | FIFO_STATUS => word.of_Z (base + UART_FIFO_STATUS_REG_OFFSET)
    | OVRD => word.of_Z (base + UART_OVRD_REG_OFFSET)
    | VAL => word.of_Z (base + UART_VAL_REG_OFFSET)
    | TIMEOUT_CTRL => word.of_Z (base + UART_TIMEOUT_CTRL_REG_OFFSET)
    end.

  Lemma reg_addr_unique r1 r2 :
    reg_addr r1 = reg_addr r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; cbn; intros H; try reflexivity.
    all:apply word.of_Z_inj_small in H; cbv; intuition discriminate.
  Qed.

  Lemma reg_addr_aligned r : word.unsigned (reg_addr r) mod 4 = 0.
  Proof.
    destruct r; cbv [reg_addr]; rewrite word.unsigned_of_Z; eauto.
  Qed.

  Inductive state : Type :=
  | IDLE
  | BUSY (txlvl : nat).

  Definition status_matches_state (s : state) (status : word) : bool :=
    (* we only specify TX flags for now *)
    match s with
    | IDLE =>
      (negb (is_flag_set status UART_STATUS_TXFULL_BIT))
       && is_flag_set status UART_STATUS_TXEMPTY_BIT
       && is_flag_set status UART_STATUS_TXIDLE_BIT
    | BUSY t =>
      if Nat.eqb t 0 then
        (* FIFO is empty *)
        is_flag_set status UART_STATUS_TXEMPTY_BIT &&
        negb (is_flag_set status UART_STATUS_TXFULL_BIT) &&
        negb (is_flag_set status UART_STATUS_TXIDLE_BIT)
      else if Nat.ltb t 32 then
        negb (is_flag_set status UART_STATUS_TXFULL_BIT) &&
        negb (is_flag_set status UART_STATUS_TXEMPTY_BIT) &&
        negb (is_flag_set status UART_STATUS_TXIDLE_BIT)
      else
        (* FIFO is full *)
        negb (is_flag_set status UART_STATUS_TXEMPTY_BIT) &&
        is_flag_set status UART_STATUS_TXFULL_BIT &&
        negb (is_flag_set status UART_STATUS_TXIDLE_BIT)
    end.

  Definition read_step
    (s : state) (r : Register) (val : word) (s' : state) : Prop :=
    match r with
    | STATUS =>
        match s with
        | IDLE => status_matches_state s val = true /\ s' = IDLE
        | BUSY O =>
            (status_matches_state s val = true /\ s' = IDLE)
        | BUSY txlvl =>
            (status_matches_state s val = true /\ s' = BUSY (txlvl - 1))
        end
    | _ => False (* cannot read any other regs *)
    end.

  Definition write_step
    (s : state) (r : Register) (val : word) (s' : state) : Prop :=
    match r with
    | WDATA =>
        match s with
        | IDLE => s' = BUSY 1
            (* writing to 4-byte WDATA reg fills the FIFO with the last byte *)
        | BUSY tx => if Nat.leb tx 32 then s' = BUSY (tx + 1) else False
        end
    | INTR_ENABLE => s' = s
    | INTR_TEST => s' = s
    | CTRL => s' = s
    | FIFO_CTRL => s' = s
    | OVRD => s' = s
    | VAL => s' = s
    | TIMEOUT_CTRL => s' = s
    | _ => False (* cannot write to other regs *)
    end.

  Global Instance uart_state_machine : state_machine.parameters := {
    state_machine.state := state ;
    state_machine.register := Register;
    state_machine.is_initial_state := eq IDLE;
    state_machine.read_step sz s a v s' := sz = 4%nat /\ read_step s a v s' ;
    state_machine.write_step sz s a v s' := sz = 4%nat /\ write_step s a v s';
    state_machine.reg_addr := reg_addr;
    state_machine.isMMIOAddr a :=
      List.Exists (fun r =>
        word.unsigned (reg_addr r) <= word.unsigned a < word.unsigned (reg_addr r) + 4
      ) all_regs;
  }.

  Global Instance uart_state_machine_ok : state_machine.ok uart_state_machine.
  Proof.
    constructor;
      unfold state_machine.isMMIOAddr; cbn;
      intros;
      try exact _;
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             end;
      subst;
      try eapply Exists_exists;
      eauto using all_regs_complete, reg_addr_aligned, reg_addr_unique with zarith;
      try ZnWords.
  Qed.
End WithParameters.
