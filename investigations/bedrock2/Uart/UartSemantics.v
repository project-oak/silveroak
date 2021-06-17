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
Require Import Bedrock2Experiments.Uart.Constants.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.Word.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

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
  Import parameters.
  Context {p : parameters} {p_ok : parameters.ok p}.
  Context {consts : uart_constants Z} {consts_ok : uart_constants_ok consts}
          {circuit_spec : circuit_behavior}.

  Add Ring wring : (Properties.word.ring_theory (word := parameters.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := parameters.word)),
         constants [Properties.word_cst]).

  Local Notation bedrock2_event := (mem * string * list word * (mem * list word))%type.
  Local Notation bedrock2_trace := (list bedrock2_event).

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

  Lemma uart_reg_addrs_eq : uart_reg_addrs = map reg_addr all_regs.
  Proof.
    cbv [uart_reg_addrs]. simpl. repeat (f_equal; try ring).
  Qed.

  Lemma reg_addr_unique r1 r2 :
    reg_addr r1 = reg_addr r2 -> r1 = r2.
  Proof.
    assert (NoDup (map reg_addr all_regs)) as N. {
      rewrite <- uart_reg_addrs_eq.
      apply addrs_unique.
    }
    eapply FinFun.Injective_carac.
    - unfold FinFun.Listing. split.
      + eapply NoDup_map_inv. exact N.
      + unfold FinFun.Full. eapply all_regs_complete.
    - exact N.
  Qed.

  Lemma reg_addr_aligned r : word.unsigned (reg_addr r) mod 4 = 0.
  Proof.
    pose proof addrs_aligned as Haligned.
    rewrite uart_reg_addrs_eq in Haligned.
    rewrite Forall_forall in Haligned.
    apply Haligned. apply in_map_iff.
    eexists; eauto using all_regs_complete.
  Qed.

  Lemma reg_addr_small r : word.unsigned (reg_addr r) + 4 <= 2 ^ 32.
  Proof.
    pose proof addrs_small as Hsmall.
    rewrite uart_reg_addrs_eq in Hsmall.
    rewrite Forall_forall in Hsmall.
    apply Hsmall. apply in_map_iff.
    eexists; eauto using all_regs_complete.
  Qed.

  Inductive state : Type :=
  | UNINITIALIZED
  | AVAILABLE (txlvl : Z) (rxlvl : Z).

  Definition status_matches_state (s : state) (status : word) : bool :=
    match s with
    | UNINITIALIZED =>
      (negb (is_flag_set status UART_STATUS_TXFULL_BIT)
       && negb (is_flag_set status UART_STATUS_RXFULL_BIT)
       && negb (is_flag_set status UART_STATUS_TXEMPTY_BIT)
       && negb (is_flag_set status UART_STATUS_TXIDLE_BIT)
       && negb (is_flag_set status UART_STATUS_RXIDLE_BIT)
       && negb (is_flag_set status UART_STATUS_RXEMPTY_BIT))
    | AVAILABLE t r =>
      if Z.eqb t 0 then
        is_flag_set status UART_STATUS_TXEMPTY_BIT &&
        is_flag_set status UART_STATUS_TXIDLE_BIT &&
        negb (is_flag_set status UART_STATUS_TXFULL_BIT)
      else if Z.eqb t 32  then
        is_flag_set status UART_STATUS_TXFULL_BIT &&
        negb (is_flag_set status UART_STATUS_TXIDLE_BIT) &&
        negb (is_flag_set status UART_STATUS_TXEMPTY_BIT)
      else
        negb (is_flag_set status UART_STATUS_TXFULL_BIT) &&
        is_flag_set status UART_STATUS_TXIDLE_BIT &&
        negb (is_flag_set status UART_STATUS_TXEMPTY_BIT)
    end.

  Definition read_step
    (s : state) (r : Register) (val : word) (s' : state) : Prop :=
    match s with
    | _ => 1 = 1 (* placeholder *)
    end.

  Definition write_step
    (s : state) (r : Register) (val : word) (s' : state) : Prop :=
    match s with
    | _ => 1 = 1 (* placeholder *)
    end.

  Global Instance state_machine_parameters
    : StateMachineSemantics.parameters 32 word mem :=
    {| StateMachineSemantics.parameters.state := state ;
       StateMachineSemantics.parameters.register := Register ;
       StateMachineSemantics.parameters.initial_state := UNINITIALIZED ;
       StateMachineSemantics.parameters.read_step := read_step ;
       StateMachineSemantics.parameters.write_step := write_step ;
       StateMachineSemantics.parameters.reg_addr := reg_addr ;
       StateMachineSemantics.parameters.all_regs := all_regs;
    |}.
  Global Instance state_machine_parameters_ok
    : StateMachineSemantics.parameters.ok state_machine_parameters.
  Proof.
    constructor.
    { left; exact eq_refl. }
    { exact word_ok. }
    { exact mem_ok. }
    { exact reg_addr_unique. }
    { exact all_regs_complete. }
    { exact reg_addr_aligned. }
    { exact reg_addr_small. }
  Defined.

End WithParameters.
