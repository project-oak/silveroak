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
      mem :> Interface.map.map word Byte.byte;
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
    }.
End parameters.
Notation parameters := parameters.parameters.

Section WithParameters.
  Import parameters.
  Context {p : parameters} {p_ok : parameters.ok p}.
  Context {consts : aes_constants Z}
          {consts_ok : aes_constants_ok constant_words}
          {timing : timing}.
  Existing Instance constant_words.

  Add Ring wring : (Properties.word.ring_theory (word := parameters.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := parameters.word)),
         constants [Properties.word_cst]).

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

  Lemma aes_reg_addrs_eq : aes_reg_addrs = map reg_addr all_regs.
  Proof.
    cbv [aes_reg_addrs].
    rewrite nregs_key_eq, nregs_iv_eq, nregs_data_eq.
    cbv [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. cbn.
    repeat (f_equal; try ring).
  Qed.

  Lemma reg_addr_unique r1 r2 :
    reg_addr r1 = reg_addr r2 -> r1 = r2.
  Proof.
    assert (NoDup (map reg_addr all_regs)) as N. {
      rewrite <-aes_reg_addrs_eq.
      pose proof addrs_unique as U. unfold unique_words in U. rewrite <- U.
      eapply List.NoDup_dedup.
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
    rewrite aes_reg_addrs_eq in Haligned.
    rewrite Forall_forall in Haligned.
    apply Haligned. apply in_map_iff.
    eexists; eauto using all_regs_complete.
  Qed.

  Lemma reg_addr_small r : word.unsigned (reg_addr r) + 4 <= 2 ^ 32.
  Proof.
    pose proof addrs_small as Hsmall.
    rewrite aes_reg_addrs_eq in Hsmall.
    rewrite Forall_forall in Hsmall.
    apply Hsmall. apply in_map_iff.
    eexists; eauto using all_regs_complete.
  Qed.

  Record aes_input :=
    { is_decrypt : bool;
      iv0 : word;
      iv1 : word;
      iv2 : word;
      iv3 : word;
      key0 : word;
      key1 : word;
      key2 : word;
      key3 : word;
      key4 : word;
      key5 : word;
      key6 : word;
      key7 : word;
      data_in0 : word;
      data_in1 : word;
      data_in2 : word;
      data_in3 : word;
    }.
  Record aes_output :=
    { data_out0 : word;
      data_out1 : word;
      data_out2 : word;
      data_out3 : word; }.

  Record idle_data :=
    { idle_ctrl : word;
      idle_iv0 : option word;
      idle_iv1 : option word;
      idle_iv2 : option word;
      idle_iv3 : option word;
      idle_key0 : option word;
      idle_key1 : option word;
      idle_key2 : option word;
      idle_key3 : option word;
      idle_key4 : option word;
      idle_key5 : option word;
      idle_key6 : option word;
      idle_key7 : option word;
      idle_data_in0 : option word;
      idle_data_in1 : option word;
      idle_data_in2 : option word;
      idle_data_in3 : option word;
    }.
  Record busy_data :=
    { busy_ctrl : word;
      busy_exp_output : aes_output;
      busy_max_cycles_until_done : nat;
    }.
  Record done_data :=
    { done_ctrl : word;
      done_data_out0 : option word;
      done_data_out1 : option word;
      done_data_out2 : option word;
      done_data_out3 : option word;
    }.

  (* state *from the perspective of the software* *)
  Inductive state : Type :=
  | UNINITIALIZED
  | IDLE (data : idle_data)
  | BUSY (data : busy_data)
  | DONE (data : done_data)
  (* TODO: add CLEAR state for aes_clear *)
  .

  (* Flags: IDLE, STALL, OUTPUT_VALID, INPUT_READY *)
  Definition status_matches_state (s : state) (status : word) : bool :=
    match s with
    | UNINITIALIZED =>
      (negb (is_flag_set status AES_STATUS_IDLE)
       && negb (is_flag_set status AES_STATUS_STALL)
       && negb (is_flag_set status AES_STATUS_OUTPUT_VALID)
       && negb (is_flag_set status AES_STATUS_INPUT_READY))
    | IDLE _ =>
      (is_flag_set status AES_STATUS_IDLE
       && negb (is_flag_set status AES_STATUS_STALL)
       && negb (is_flag_set status AES_STATUS_OUTPUT_VALID)
       && is_flag_set status AES_STATUS_INPUT_READY)
    | BUSY _ =>
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

  Definition aes_expected_output (input : aes_input) : aes_output :=
    let (is_decrypt, iv0, iv1, iv2, iv3,
         key0, key1, key2, key3, key4, key5, key6, key7,
         data_in0, data_in1, data_in2, data_in3) := input in
    let '(out0, out1, out2, out3) :=
        aes_spec is_decrypt
                 (key0, key1, key2, key3, key4, key5, key6, key7)
                 (iv0, iv1, iv2, iv3)
                 (data_in0, data_in1, data_in2, data_in3) in
    {| data_out0 := out0 ;
       data_out1 := out1 ;
       data_out2 := out2 ;
       data_out3 := out3 ; |}.

  Definition get_aes_input (data : idle_data) : option aes_input :=
    match data with
    | Build_idle_data
        ctrl (Some iv0) (Some iv1) (Some iv2) (Some iv3)
        (Some key0) (Some key1) (Some key2) (Some key3)
        (Some key4) (Some key5) (Some key6) (Some key7)
        (Some data_in0) (Some data_in1) (Some data_in2) (Some data_in3) =>
      Some (Build_aes_input
              (is_flag_set ctrl AES_CTRL_OPERATION)
              iv0 iv1 iv2 iv3
              key0 key1 key2 key3 key4 key5 key6 key7
              data_in0 data_in1 data_in2 data_in3)
    | _ => None
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

  Definition done_data_from_output (ctrl : word) (out : aes_output) : done_data :=
    Build_done_data ctrl (Some (data_out0 out)) (Some (data_out1 out))
                    (Some (data_out2 out)) (Some (data_out3 out)).

  Definition read_output_reg (r : Register) (data : done_data)
    : option (word * done_data) :=
    let ctrl := done_ctrl data in
    let o0 := done_data_out0 data in
    let o1 := done_data_out1 data in
    let o2 := done_data_out2 data in
    let o3 := done_data_out3 data in
    match r with
    | DATA_OUT0 =>
      match o0 with
      | Some o0 => Some (o0, Build_done_data ctrl None o1 o2 o3)
      | None => None
      end
    | DATA_OUT1 =>
      match o1 with
      | Some o1 => Some (o1, Build_done_data ctrl o0 None o2 o3)
      | None => None
      end
    | DATA_OUT2 =>
      match o2 with
      | Some o2 => Some (o2, Build_done_data ctrl o0 o1 None o3)
      | None => None
      end
    | DATA_OUT3 =>
      match o3 with
      | Some o3 => Some (o3, Build_done_data ctrl o0 o1 o2 None)
      | None => None
      end
    | _ => None
    end.

  Definition read_step
             (s : state) (r : Register) (val : word) (s' : state) : Prop :=
    match reg_category r with
    | StatusReg =>
      (* status register read *)
      match s with
      | BUSY (Build_busy_data ctrl out n) =>
        if is_flag_set val AES_STATUS_OUTPUT_VALID
        then
          (* transition to DONE state *)
          s' = DONE (done_data_from_output ctrl out)
        else
          (* decrement max #cycles until done *)
          status_matches_state s val = true (* we must have read BUSY status *)
          /\ match n with
            | O => False (* exceeded max #cycles *)
            | S n' => s' = BUSY (Build_busy_data ctrl out n')
            end
      | _ =>
        (* if the status is not busy, reading the status causes no change *)
        status_matches_state s val = true /\ s' = s
      end
    | DataOutReg =>
      (* output data register read *)
      match s with
      | DONE data =>
        exists data',
        read_output_reg r data = Some (val, data')
        /\ s' = match data' with
               | Build_done_data ctrl None None None None =>
                 (* all output registers read; transition to IDLE state *)
                 IDLE (Build_idle_data
                         ctrl None None None None None None None None
                         None None None None None None None None)
               | _ =>
                 (* some registers have not been read; stay in DONE state *)
                 DONE data'
               end
      | _ => False (* read is not permitted from other states *)
      end
    | ControlReg | DataInReg | KeyReg | IVReg => False (* not readable *)
    end.

  Definition write_input_reg (r : Register) (data : idle_data) (val : word)
    : idle_data :=
    let ctrl := idle_ctrl data in
    let iv0 := idle_iv0 data in
    let iv1 := idle_iv1 data in
    let iv2 := idle_iv2 data in
    let iv3 := idle_iv3 data in
    let key0 := idle_key0 data in
    let key1 := idle_key1 data in
    let key2 := idle_key2 data in
    let key3 := idle_key3 data in
    let key4 := idle_key4 data in
    let key5 := idle_key5 data in
    let key6 := idle_key6 data in
    let key7 := idle_key7 data in
    let data_in0 := idle_data_in0 data in
    let data_in1 := idle_data_in1 data in
    let data_in2 := idle_data_in2 data in
    let data_in3 := idle_data_in3 data in
    match r with
    | IV0 => Build_idle_data
              ctrl (Some val) iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
              data_in0 data_in1 data_in2 data_in3
    | IV1 => Build_idle_data
              ctrl iv0 (Some val) iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
              data_in0 data_in1 data_in2 data_in3
    | IV2 => Build_idle_data
              ctrl iv0 iv1 (Some val) iv3 key0 key1 key2 key3 key4 key5 key6 key7
              data_in0 data_in1 data_in2 data_in3
    | IV3 => Build_idle_data
              ctrl iv0 iv1 iv2 (Some val) key0 key1 key2 key3 key4 key5 key6 key7
              data_in0 data_in1 data_in2 data_in3
    | KEY0 => Build_idle_data
               ctrl iv0 iv1 iv2 iv3 (Some val) key1 key2 key3 key4 key5 key6 key7
               data_in0 data_in1 data_in2 data_in3
    | KEY1 => Build_idle_data
               ctrl iv0 iv1 iv2 iv3 key0 (Some val) key2 key3 key4 key5 key6 key7
               data_in0 data_in1 data_in2 data_in3
    | KEY2 => Build_idle_data
               ctrl iv0 iv1 iv2 iv3 key0 key1 (Some val) key3 key4 key5 key6 key7
               data_in0 data_in1 data_in2 data_in3
    | KEY3 => Build_idle_data
               ctrl iv0 iv1 iv2 iv3 key0 key1 key2 (Some val) key4 key5 key6 key7
               data_in0 data_in1 data_in2 data_in3
    | KEY4 => Build_idle_data
               ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 (Some val) key5 key6 key7
               data_in0 data_in1 data_in2 data_in3
    | KEY5 => Build_idle_data
               ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 (Some val) key6 key7
               data_in0 data_in1 data_in2 data_in3
    | KEY6 => Build_idle_data
               ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 (Some val) key7
               data_in0 data_in1 data_in2 data_in3
    | KEY7 => Build_idle_data
               ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 (Some val)
               data_in0 data_in1 data_in2 data_in3
    | DATA_IN0 => Build_idle_data
                   ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
                   (Some val) data_in1 data_in2 data_in3
    | DATA_IN1 => Build_idle_data
                   ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
                   data_in0 (Some val) data_in2 data_in3
    | DATA_IN2 => Build_idle_data
                   ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
                   data_in0 data_in1 (Some val) data_in3
    | DATA_IN3 => Build_idle_data
                   ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
                   data_in0 data_in1 data_in2 (Some val)
    | _ => Build_idle_data
            ctrl iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
            data_in0 data_in1 data_in2 data_in3
    end.

  Definition write_step
             (s : state) (r : Register) (val : word) (s' : state) : Prop :=
    match reg_category r with
    | ControlReg =>
      match s with
      | UNINITIALIZED =>
        (* transition to IDLE state *)
        s' = IDLE (Build_idle_data
                     val None None None None None None None None
                     None None None None None None None None)
      | IDLE (Build_idle_data
                _ iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
                data_in0 data_in1 data_in2 data_in3) =>
        (* stay IDLE, update ctrl value *)
        s' = IDLE (Build_idle_data
                     val iv0 iv1 iv2 iv3 key0 key1 key2 key3 key4 key5 key6 key7
                     data_in0 data_in1 data_in2 data_in3)
      | _ => False (* ctrl register is not writeable in other states *)
      end
    | KeyReg | IVReg =>
      match s with
      | IDLE data => s' = IDLE (write_input_reg r data val)
      | _ => False (* key/iv registers are not writeable in other states *)
      end
    | DataInReg =>
      match s with
      | IDLE data =>
        let data' := write_input_reg r data val in
        s' = match get_aes_input data' with
             | Some input =>
               (* input registers are fully populated; encryption begins *)
               BUSY (Build_busy_data
                       (idle_ctrl data')
                       (aes_expected_output input) timing.ndelays_core)
             | None =>
               (* more input registers needed; stay in IDLE state *)
               IDLE data'
             end
      | _ => False (* input data registers not writeable in other states *)
      end
    | DataOutReg | StatusReg => False (* not writeable *)
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
