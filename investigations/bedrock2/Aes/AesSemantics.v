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
Require Import Bedrock2Experiments.Aes.Constants.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.Word.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Loosely based on bedrock2/FE310CSemantics.v *)

Definition option_bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some a => f a
  | None => None
  end.
Local Notation "y <- x ;; f" := (option_bind x (fun y => f))
                                  (at level 61, right associativity).

(* Circuit timing properties *)
Module timing.
  Class timing :=
    { ndelays_core : nat; (* number of delays on AES core datapath *)
    }.
End timing.
Notation timing := timing.timing.

Module parameters.
  Class parameters :=
    { word :> Interface.word.word 32;
      mem :> Interface.map.map word.rep Byte.byte;
      regs :> Interface.map.map word.rep word.rep; (* register values *)
      (* TODO: mode is currently ignored *)
      aes_spec :
        forall (is_decrypt : bool)
          (key : word * word * word * word * word * word * word * word)
          (iv data : word * word * word * word),
          word * word * word * word
    }.

  Class ok (p : parameters) :=
    { word_ok :> word.ok word; (* for impl of mem below *)
      mem_ok :> Interface.map.ok mem; (* for impl of mem below *)
      regs_ok :> Interface.map.ok regs;
    }.
End parameters.
Notation parameters := parameters.parameters.

Definition READ := "REG32_GET".
Definition WRITE := "REG32_SET".

Section WithParameters.
  Import parameters.
  Context {p : parameters} {p_ok : parameters.ok p}.
  Context {consts : aes_constants Z} {timing : timing}.
  Existing Instance constant_words.

  Local Notation bedrock2_event := (mem * string * list word * (mem * list word))%type.
  Local Notation bedrock2_trace := (list bedrock2_event).

  Inductive Register : Set :=
  | CTRL
  | STATUS
  | KEY0
  | KEY1
  | KEY2
  | KEY3
  | KEY4
  | KEY5
  | KEY6
  | KEY7
  | IV0
  | IV1
  | IV2
  | IV3
  | DATA_IN0
  | DATA_IN1
  | DATA_IN2
  | DATA_IN3
  | DATA_OUT0
  | DATA_OUT1
  | DATA_OUT2
  | DATA_OUT3
  .

  Definition all_regs : list Register :=
    [ CTRL ; STATUS
      ; KEY0 ; KEY1 ; KEY2 ; KEY3 ; KEY4 ; KEY5 ; KEY6 ; KEY7
      ; IV0 ; IV1 ; IV2 ; IV3
      ; DATA_IN0 ; DATA_IN1 ; DATA_IN2 ; DATA_IN3
      ; DATA_OUT0 ; DATA_OUT1 ; DATA_OUT2 ; DATA_OUT3 ].

  Lemma all_regs_complete r : In r all_regs.
  Proof. cbv [all_regs In]. destruct r; tauto. Qed.

  Definition reg_addr (r : Register) : word :=
    match r with
    | CTRL => AES_CTRL
    | STATUS => AES_STATUS
    | KEY0 => AES_KEY0
    | KEY1 => word.add AES_KEY0 (word.of_Z 4)
    | KEY2 => word.add AES_KEY0 (word.of_Z 8)
    | KEY3 => word.add AES_KEY0 (word.of_Z 12)
    | KEY4 => word.add AES_KEY0 (word.of_Z 16)
    | KEY5 => word.add AES_KEY0 (word.of_Z 20)
    | KEY6 => word.add AES_KEY0 (word.of_Z 24)
    | KEY7 => word.add AES_KEY0 (word.of_Z 28)
    | IV0 => AES_IV0
    | IV1 => word.add AES_IV0 (word.of_Z 4)
    | IV2 => word.add AES_IV0 (word.of_Z 8)
    | IV3 => word.add AES_IV0 (word.of_Z 12)
    | DATA_IN0 => AES_DATA_IN0
    | DATA_IN1 => word.add AES_DATA_IN0 (word.of_Z 4)
    | DATA_IN2 => word.add AES_DATA_IN0 (word.of_Z 8)
    | DATA_IN3 => word.add AES_DATA_IN0 (word.of_Z 12)
    | DATA_OUT0 => AES_DATA_OUT0
    | DATA_OUT1 => word.add AES_DATA_OUT0 (word.of_Z 4)
    | DATA_OUT2 => word.add AES_DATA_OUT0 (word.of_Z 8)
    | DATA_OUT3 => word.add AES_DATA_OUT0 (word.of_Z 12)
    end.

  Definition known_register_state : Type := map.rep (map:=regs).

  Definition reg_lookup (rs : known_register_state) (r : Register) : option word :=
    map.get rs (reg_addr r).

  Record aes_output :=
    { data_out0 : word;
      data_out1 : word;
      data_out2 : word;
      data_out3 : word; }.

  (* state *from the perspective of the software* *)
  Inductive state : Type :=
  | UNINITIALIZED (* CTRL register not yet written *)
  | IDLE (rs : known_register_state)
  | BUSY (rs : known_register_state)
         (exp_output : aes_output)
         (max_cycles_until_done : nat)
  | DONE (rs : known_register_state)
  (* TODO: add CLEAR state for aes_clear *)
  .

  (* Flags: IDLE, STALL, OUTPUT_VALID, INPUT_READY *)
  Definition status_matches_state (s : state) (status : word) : bool :=
    match s with
    | UNINITIALIZED =>
      (is_flag_set status AES_STATUS_IDLE
       && negb (is_flag_set status AES_STATUS_STALL)
       && negb (is_flag_set status AES_STATUS_OUTPUT_VALID)
       && negb (is_flag_set status AES_STATUS_INPUT_READY))
    | IDLE _ =>
      (is_flag_set status AES_STATUS_IDLE
       && negb (is_flag_set status AES_STATUS_STALL)
       && negb (is_flag_set status AES_STATUS_OUTPUT_VALID)
       && is_flag_set status AES_STATUS_INPUT_READY)
    | BUSY _ _ _ =>
      (negb (is_flag_set status AES_STATUS_IDLE)
       && negb (is_flag_set status AES_STATUS_STALL)
       && negb (is_flag_set status AES_STATUS_OUTPUT_VALID)
       && negb (is_flag_set status AES_STATUS_INPUT_READY))
    | DONE _ =>
      (* STALL can be either true or false here *)
      (negb (is_flag_set status AES_STATUS_IDLE)
       && is_flag_set status AES_STATUS_OUTPUT_VALID
       && negb (is_flag_set status AES_STATUS_INPUT_READY))
    end.

  Definition aes_expected_output (rs : known_register_state) : option aes_output :=
    ctrl <- reg_lookup rs CTRL ;;
    key0 <- reg_lookup rs KEY0 ;;
    key1 <- reg_lookup rs KEY1 ;;
    key2 <- reg_lookup rs KEY2 ;;
    key3 <- reg_lookup rs KEY3 ;;
    key4 <- reg_lookup rs KEY4 ;;
    key5 <- reg_lookup rs KEY5 ;;
    key6 <- reg_lookup rs KEY6 ;;
    key7 <- reg_lookup rs KEY7 ;;
    iv0 <- reg_lookup rs IV0 ;;
    iv1 <- reg_lookup rs IV1 ;;
    iv2 <- reg_lookup rs IV2 ;;
    iv3 <- reg_lookup rs IV3 ;;
    data_in0 <- reg_lookup rs DATA_IN0 ;;
    data_in1 <- reg_lookup rs DATA_IN1 ;;
    data_in2 <- reg_lookup rs DATA_IN2 ;;
    data_in3 <- reg_lookup rs DATA_IN3 ;;
    let is_decrypt := is_flag_set ctrl AES_CTRL_OPERATION in
    let '(out0, out1, out2, out3) :=
        aes_spec is_decrypt
                 (key0, key1, key2, key3, key4, key5, key6, key7)
                 (iv0, iv1, iv2, iv3)
                 (data_in0, data_in1, data_in2, data_in3) in
    Some {| data_out0 := out0 ;
            data_out1 := out1 ;
            data_out2 := out2 ;
            data_out3 := out3 ; |}.

  Definition is_busy (s : state) : bool :=
    match s with
    | BUSY _ _ _ => true
    | _ => false
    end.

  Inductive RegisterCategory : Set :=
  | ControlReg
  | StatusReg
  | KeyReg
  | IVReg
  | DataInReg
  | DataOutReg
  .

  Definition reg_category (r : Register) : RegisterCategory :=
    match r with
    | CTRL => ControlReg
    | STATUS => StatusReg
    | KEY0 => KeyReg
    | KEY1 => KeyReg
    | KEY2 => KeyReg
    | KEY3 => KeyReg
    | KEY4 => KeyReg
    | KEY5 => KeyReg
    | KEY6 => KeyReg
    | KEY7 => KeyReg
    | IV0 => IVReg
    | IV1 => IVReg
    | IV2 => IVReg
    | IV3 => IVReg
    | DATA_IN0 => DataInReg
    | DATA_IN1 => DataInReg
    | DATA_IN2 => DataInReg
    | DATA_IN3 => DataInReg
    | DATA_OUT0 => DataOutReg
    | DATA_OUT1 => DataOutReg
    | DATA_OUT2 => DataOutReg
    | DATA_OUT3 => DataOutReg
    end.

  Definition reg_category_eqb (c1 c2 : RegisterCategory) : bool :=
    match c1, c2 with
    | ControlReg, ControlReg
    | StatusReg, StatusReg
    | KeyReg, KeyReg
    | IVReg, IVReg
    | DataInReg, DataInReg
    | DataOutReg, DataOutReg => true
    | _,_ => false
    end.

  Global Instance reg_category_eqb_spec : EqDecider reg_category_eqb.
  Proof. intros x y. destruct x,y; constructor; congruence. Qed.

  Definition addr_in_category (addr : word) (c : RegisterCategory) : bool :=
    existsb (fun r => (word.eqb (reg_addr r) addr
                    && reg_category_eqb c (reg_category r))%bool)
            all_regs.

  (* gives the number of populated registers in the given category *)
  Definition nregs_populated
             (rs : known_register_state)
             (cat : RegisterCategory) : nat :=
    map.fold
      (map:=regs)
      (fun acc addr _ => if addr_in_category addr cat
                      then S acc
                      else acc) 0%nat rs.

  Definition set_out_regs
             (rs : known_register_state) (out : aes_output) : known_register_state :=
    let rs := map.put rs (reg_addr DATA_OUT0) out.(data_out0) in
    let rs := map.put rs (reg_addr DATA_OUT1) out.(data_out1) in
    let rs := map.put rs (reg_addr DATA_OUT2) out.(data_out2) in
    map.put rs (reg_addr DATA_OUT3) out.(data_out3).

  Definition unset_inp_regs
             (rs : known_register_state) : known_register_state :=
    let rs := map.remove rs (reg_addr KEY0) in
    let rs := map.remove rs (reg_addr KEY1) in
    let rs := map.remove rs (reg_addr KEY2) in
    let rs := map.remove rs (reg_addr KEY3) in
    let rs := map.remove rs (reg_addr KEY4) in
    let rs := map.remove rs (reg_addr KEY5) in
    let rs := map.remove rs (reg_addr KEY6) in
    let rs := map.remove rs (reg_addr KEY7) in
    let rs := map.remove rs (reg_addr IV0) in
    let rs := map.remove rs (reg_addr IV1) in
    let rs := map.remove rs (reg_addr IV2) in
    let rs := map.remove rs (reg_addr IV3) in
    let rs := map.remove rs (reg_addr DATA_IN0) in
    let rs := map.remove rs (reg_addr DATA_IN1) in
    let rs := map.remove rs (reg_addr DATA_IN2) in
    let rs := map.remove rs (reg_addr DATA_IN3) in
    rs.

  Definition read_step
             (s : state) (r : Register) (val : word) (s' : state) : Prop :=
    match reg_category r with
    | StatusReg =>
      (* status register read *)
      match s with
      | BUSY rs out n =>
        if status_matches_state (DONE rs) val
        then
          (* transition to DONE state *)
          s' = DONE (set_out_regs rs out)
        else
          (* decrement max #cycles until done *)
          status_matches_state s val = true (* we must have read BUSY status *)
          /\ match n with
            | O => False (* exceeded max #cycles *)
            | S n' => s' = BUSY rs out n'
            end
      | _ =>
        (* if the status is not busy, reading the status causes no change *)
        status_matches_state s val = true /\ s' = s
      end
    | DataOutReg =>
      (* output data register read *)
      match s with
      | DONE rs =>
        reg_lookup rs r = Some val
        /\ let rs' := map.remove rs (reg_addr r) in
          if (nregs_populated rs' DataOutReg =? 0)%nat
          then
            (* all output registers have been read; transition to IDLE state *)
            s' = IDLE rs'
          else
            (* stay in DONE state *)
            s' = DONE rs'
      | _ => False (* cannot read from output registers unless DONE *)
      end
    | _ => False (* no guarantees about the values of other registers *)
    end.

  Definition write_step
             (s : state) (r : Register) (val : word) (s' : state) : Prop :=
    match reg_category r with
    | ControlReg =>
      match s with
      | UNINITIALIZED =>
        (* transition to IDLE state *)
        s' = IDLE (map.put map.empty AES_CTRL val)
      | IDLE rs =>
        (* stay IDLE, update ctrl value *)
        s' = IDLE (map.put rs AES_CTRL val)
      | _ => False (* ctrl register is not writeable in other states *)
      end
    | KeyReg | IVReg =>
      match s with
      | IDLE rs =>
        s' = IDLE (map.put rs (reg_addr r) val)
      | _ => False (* key/iv registers are not writeable in other states *)
      end
    | DataInReg =>
      match s with
      | IDLE rs =>
        (* can only provide input once key/iv regs have been written *)
        nregs_populated rs KeyReg = 8%nat
        /\ nregs_populated rs IVReg = 4%nat
        /\ (nregs_populated rs DataInReg < 4)%nat
        /\ let rs' := map.put rs (reg_addr r) val in
          if (nregs_populated rs' DataInReg =? 4)%nat
          then
            (* wrote to last input register; transition to BUSY state *)
            match aes_expected_output (map.put rs (reg_addr r) val) with
            | Some out => s' = BUSY (unset_inp_regs rs') out timing.ndelays_core
            | None => False (* should not be possible *)
            end
          else
            (* more input registers needed; stay in IDLE state *)
            s' = IDLE rs'
      | _ => False (* input data registers are not writeable in other states *)
      end
    | StatusReg | DataOutReg => False (* not writeable *)
    end.

  Global Instance state_machine_parameters
    : StateMachineSemantics.parameters 32 word :=
    {| StateMachineSemantics.parameters.state := state ;
       StateMachineSemantics.parameters.register := Register ;
       StateMachineSemantics.parameters.mem := mem ;
       StateMachineSemantics.parameters.READ := READ ;
       StateMachineSemantics.parameters.WRITE := WRITE ;
       StateMachineSemantics.parameters.initial_state := UNINITIALIZED ;
       StateMachineSemantics.parameters.read_step := read_step ;
       StateMachineSemantics.parameters.write_step := write_step ;
       StateMachineSemantics.parameters.reg_addr := reg_addr ;
    |}.

  Global Instance state_machine_parameters_ok
    : StateMachineSemantics.parameters.ok state_machine_parameters.
  Proof.
    constructor.
    { left; exact eq_refl. }
    { exact word_ok. }
    { exact mem_ok. }
  Defined.

End WithParameters.
