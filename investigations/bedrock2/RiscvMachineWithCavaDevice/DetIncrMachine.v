Require Import Cava.Cava.
Import Circuit.Notations.
Require Import Cava.CavaProperties.


Section WithCava.
  Context {signal} {semantics : Cava signal}.

  (* TODO doesn't Cava already provide these? *)
  Definition ite{T: SignalType}(cond: signal Bit)(thn els: signal T):
    cava (signal T) :=
    branches <- packV (Vector.of_list [els; thn]);;
    ctrl <- packV (Vector.of_list [cond]);;
    indexAt branches ctrl.

  Definition and3: signal Bit * signal Bit * signal Bit -> cava (signal Bit) :=
    fun '(x1, x2, x3) => x12 <- and2 (x1, x2);; and2 (x12, x3).

  Definition or3: signal Bit * signal Bit * signal Bit -> cava (signal Bit) :=
    fun '(x1, x2, x3) => x12 <- or2 (x1, x2);; or2 (x12, x3).

  Definition incr_update:
    (* input: *)
    signal Bit *             (* is_read_req *)
    signal Bit *             (* is_write_req *)
    signal (Vec Bit 32) *    (* req_addr (only relevant if is_reaq_req or is_write_req) *)
    signal (Vec Bit 32) *    (* req_value (only relevant if is_write_req *)
    (* state: *)
    signal Bit *             (* idle *)
    signal Bit *             (* busy *)
    signal Bit *             (* done *)
    signal (Vec Bit 32)      (* value *)
    -> cava (
    (* output: *)
    signal Bit *             (* is_resp *)
    signal (Vec Bit 32) *    (* resp (only relevant if is_resp *)
    (* state: *)
    signal Bit *             (* idle *)
    signal Bit *             (* busy *)
    signal Bit *             (* done *)
    signal (Vec Bit 32))     (* value *)
  := fun '(is_read_req, is_write_req, req_addr, req_value, idle, busy, done, value) =>
       initialized <- or3 (idle, busy, done);;
       idle <- ite initialized idle (constant true);;
       is_resp <- or2 (is_read_req, is_write_req);;
       (* bit #2 of the address determines if STATUS or VALUE register *)
       req_addr1 <- Vec.tl req_addr;;
       req_addr2 <- Vec.tl req_addr1;;
       is_status_req <- Vec.hd req_addr2;;
       is_value_req <- inv is_status_req;;
       is_value_write_req <- and2 (is_value_req, is_write_req);;
       isnt_value_write_req <- inv is_value_write_req;;
       is_value_read_req <- and2 (is_value_req, is_read_req);;
       no_pending_inp <- inv is_resp;;
       result_ready <- or2 (busy, done);;
       done2idle <- and2 (done, is_value_read_req);;
       not_done2idle <- inv done2idle;;
       idle2idle <- and2 (idle, isnt_value_write_req);;
       idle' <- or2 (idle2idle, done2idle);;
       busy' <- is_value_write_req;;
       done' <- and2 (result_ready, not_done2idle);;
       value_plus_one <- incrN value;;
       value_or_input <- ite is_value_write_req req_value value;;
       value' <- ite busy value_plus_one value_or_input;;
       zeros <- Vec.const (constant false) 29;;
       v1 <- Vec.cons done zeros;;
       v2 <- Vec.cons busy v1;;
       v3 <- Vec.cons idle v2;;
       resp <- ite is_status_req v3 value;;
       ret (is_resp, resp, idle', busy', done', value').

  Definition incr: Circuit (signal Bit * signal Bit * signal (Vec Bit 32) * signal (Vec Bit 32))
                           (signal Bit * signal (Vec Bit 32)) :=
    Loop (Loop (Loop (Loop (Comb incr_update)))).

End WithCava.

Definition incr_device_step:
  (* input: current state, is_read_req, is_write_req, req_addr, req_value *)
  circuit_state incr -> bool * bool * Bvector 32 * Bvector 32 ->
  (* output: next state, is_resp, resp *)
  circuit_state incr * (bool * Bvector 32)
  := step incr.

Require Import coqutil.Datatypes.List.

(* like `simulate`, but also output the internal state, for more insightful debugging *)
Fixpoint simulate_with_state_rec{i o}(c: Circuit i o)(initial: circuit_state c)(inps: list i)
  : list (circuit_state c * o) :=
  match inps with
  | [] => []
  | inp :: rest => let r := step c initial inp in r :: simulate_with_state_rec c (fst r) rest
  end.
Definition simulate_with_state{i o}(c: Circuit i o): list i -> list (circuit_state c * o) :=
  simulate_with_state_rec c (reset_state c).

Example sample_trace := Eval compute in simulate_with_state incr [
  (false, false, N2Bv_sized 32 111, N2Bv_sized 32 111); (* no action *)
  (false, true, N2Bv_sized 32 0, N2Bv_sized 32 15);     (* write VALUE:=15 *)
  (true, false, N2Bv_sized 32 4, N2Bv_sized 32 111);    (* read STATUS *)
  (true, false, N2Bv_sized 32 4, N2Bv_sized 32 111);    (* read STATUS *)
  (true, false, N2Bv_sized 32 0, N2Bv_sized 32 111)     (* read VALUE *)
].

(* Print sample_trace. *)

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.Simp.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Section WithParameters.
  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Definition mk_counter_state(idle busy done: bool)(val: Bvector 32): circuit_state incr :=
    (tt, (tt, (tt, (tt, (tt, val), done), busy), idle)).

  Global Instance counter_device: device := {|
    device.state := circuit_state incr;
    device.is_ready_state s := exists val idle, s = mk_counter_state idle false false val;
    device.run1 := incr_device_step;
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay := 1;
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.

  Ltac destruct_state s :=
    destruct s as ([] & (([] & (([] & (([] & ([] & ?val)) & ?done)) & ?busy)) & ?idle)).

  Inductive counter_related: IncrementWaitSemantics.state -> circuit_state incr -> Prop :=
  | IDLE_related: forall val idle,
      (* after reset, all three bools are false, and idle will be set to true *)
      counter_related IDLE (mk_counter_state idle false false val)
  | BUSY_related: forall val ncycles,
      counter_related (BUSY val ncycles) (mk_counter_state false true false (word_to_bv val))
  | DONE_related: forall val,
      counter_related (DONE val) (mk_counter_state false false true (word_to_bv val)).

  Axiom TODO: False.

  Axiom word_to_bv_inj: forall x y, word_to_bv x = word_to_bv y -> x = y.

  Set Printing Depth 100000.

  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device state_machine_parameters.
  Proof.
    eapply Build_device_implements_state_machine with (device_state_related := counter_related);
      intros.
    - (* mmioAddrs_match: *)
      reflexivity.
    - (* initial_state_is_ready_state: *)
      simpl in *. subst. inversion H0. eauto.
    - (* initial_states_are_related: *)
      simpl in *. destruct H0 as (val & idle & H0). subst. eapply IDLE_related.
    - (* initial_state_exists: *)
      simpl in *. destruct H as (val & idle & H). subst. eauto using IDLE_related.
    - (* nonMMIO_device_step_preserves_state_machine_state: *)
      simpl in sL1, sL2. destruct_state sL1. destruct_state sL2.
      cbn [device.run1 counter_device incr_device_step step incr incr_update Loop snd
           ret bind monad CombinationalSemantics Identity.Monad_ident constant] in H0.
      eapply pair_equal_spec in H0. destruct H0 as [E1 E2].
      subst.
      eapply pair_equal_spec in E1. destruct E1 as [_ E1].
      eapply pair_equal_spec in E1. destruct E1 as [E1 E2]. simpl in E2. subst.
      eapply pair_equal_spec in E1. destruct E1 as [_ E1].
      eapply pair_equal_spec in E1. destruct E1 as [E1 E2]. simpl in E2. subst.
      eapply pair_equal_spec in E1. destruct E1 as [_ E1].
      eapply pair_equal_spec in E1. destruct E1 as [E1 E2]. simpl in E2. subst.
      eapply pair_equal_spec in E1. destruct E1 as [_ E1].
      eapply pair_equal_spec in E1. destruct E1 as [_ E1]. simpl in E1. subst.
      inversion H; subst.
      + (* IDLE_related: *)
        cbn. rewrite andb_false_r. destruct idle; cbn; simpl; eapply IDLE_related.
      + (* BUSY_related: *)
        rewrite andb_false_r. cbn -[incrN]. change (Pos.to_nat 1) with 1%nat.
        cbn -[incrN].
        (* Problem: device can go from BUSY to DONE without any software interaction *)
        case TODO.
      + (* DONE_related: *)
        cbn. rewrite andb_false_r. cbn. assumption.
    - (* state_machine_read_to_device_read: *)
      (* simpler because device.maxRespDelay=1 *)
      unfold device.maxRespDelay, device.runUntilResp, device.state, device.run1, counter_device.
      unfold StateMachineSemantics.parameters.read_step, state_machine_parameters in *.
      destruct H as [? H]. subst.
      unfold read_step in *.
      destruct r.
      + (* r=VALUE *)
        destruct sH; try contradiction. destruct H. subst.
        inversion H0; subst.
        cbn. rewrite andb_false_r. simpl.
        unfold word_to_bv. rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
        simpl. eexists. split; [reflexivity|]. eapply IDLE_related.
      + (* r=STATUS *)
        destruct sH.
        * (* sH=IDLE *)
          destruct H. subst. inversion H0. subst.
          cbn. rewrite andb_false_r. simpl. unfold status_value, STATUS_IDLE.
          unfold word_to_bv.
          rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
          rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
          eexists. destruct idle; (split; [reflexivity|]). all: eapply IDLE_related.
        * (* sH=BUSY *)
          inversion H0. subst.
          destruct H as [H | H].
          -- (* transition to DONE *)
             destruct H; subst.
             simpl (StateMachineSemantics.parameters.reg_addr _).
             unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_bv, status_value, STATUS_DONE.
             rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
             rewrite !word.unsigned_of_Z. unfold word.wrap. cbn -[Vec.hd Vec.tl incrN].
             rewrite andb_false_r. simpl.
             eexists.
             (* Problem: high-level transitions to DONE, but low-level is in BUSY and
                therefore still answers BUSY, somehow we're shifted by 1 cycle? *)
             case TODO.
          -- (* stay BUSY *)
             destruct H as (n & ? & ? & ?); subst.
             simpl (StateMachineSemantics.parameters.reg_addr _).
             unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_bv, status_value, STATUS_BUSY.
             rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
             rewrite !word.unsigned_of_Z. unfold word.wrap. cbn -[Vec.hd Vec.tl incrN].
             rewrite andb_false_r. simpl.
             eexists. split; [reflexivity|].
             (* Problem: value now off by 1 *)
             case TODO.
        * (* sH=DONE *)
          destruct H. subst. inversion H0. subst.
          simpl (StateMachineSemantics.parameters.reg_addr _).
          unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_bv, status_value, STATUS_DONE.
          rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn -[Vec.hd Vec.tl incrN].
          rewrite andb_false_r. simpl.
          eexists. split; [reflexivity|]. eapply DONE_related.
    - (* state_machine_write_to_device_write: *)
      destruct H. subst. unfold write_step in H1.
      destruct r. 2: contradiction.
      destruct sH; try contradiction. subst.
      inversion H0. subst.
      cbn.
      unfold word_to_bv.
      rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
      cbn.
      eexists _, _. split; [reflexivity|]. destruct idle; eapply BUSY_related.
  Unshelve.
  all: try exact (reset_state incr).
  Qed.

End WithParameters.
