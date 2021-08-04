From Coq Require Import
     ZArith.ZArith.

From Cava Require Import
     Expr
     Primitives
     Types.

Import ExprNotations.
Import PrimitiveNotations.

Section Var.
  Import ExprNotations.
  Context {var : tvar}.

  Local Open Scope N.

  (* Things that should probably be in cava *)
  Section Cava.
    Definition True := Constant (true: denote_type Bit).
  End Cava.

  Definition incr
    : Circuit _
              (* Input *)
              [ Bit          (* is_read_req *)
                ; Bit        (* is_write_req *)
                ; BitVec 32  (* req_addr (only relevant if is_reaq_req or is_write_req) *)
                ; BitVec 32 ](* req_value (only relevant if is_write_req *)
              (* Output *)
              (Bit             (* is_resp *)
                 ** BitVec 32) (* resp (only relevant if is_resp *)
    := {{
      fun is_read_req is_write_req req_addr req_value =>
        (* bit #2 of the address determines if STATUS or VALUE register *)
        let is_status_req := `index` req_addr `Constant (val_of (BitVec 2) 2)` in
        let is_value_req := !is_status_req in
        let is_value_write_req := is_value_req && is_write_req in
        let is_value_read_req := is_value_req && is_read_req in

        let/delay '(idle, busy, done; value) :=
           let idle1 := if idle || busy || done then idle
                        else `True` in
           let result_ready := busy || done in

           let done2idle := done && is_value_read_req in
           let idle2idle := idle1 && !is_value_write_req in

           let idle2 := idle2idle || done2idle in
           let busy' := is_value_write_req in
           let done' := result_ready && !done2idle in
           let value' := if busy then value + `_1`
                         else if is_value_write_req then req_value
                              else value in
           (idle2, busy', done', value')
             initially (false,(false,(false,0))) : denote_type (Bit ** Bit ** Bit ** BitVec 32)
        in

        let status := `_0` <<+ done <<+ busy <<+ idle in
        let resp := if is_status_req then status else value in
        let is_resp := is_read_req || is_write_req in
        (is_resp, resp)
       }}.
End Var.

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
Require Import bedrock2.ZnWords.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.StateMachineSemantics.
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
      (0 < ncycles)%nat ->
      counter_related (BUSY val ncycles) (mk_counter_state false true false (word_to_bv val))
  (* the hardware is already done, but the software hasn't polled it yet to find out,
     so we have to relate a software-BUSY to a hardware-done: *)
  | BUSY_done_related: forall val ncycles,
      counter_related (BUSY val ncycles)
                      (mk_counter_state false false true (word_to_bv (word.add (word.of_Z 1) val)))
  | DONE_related: forall val,
      counter_related (DONE val) (mk_counter_state false false true (word_to_bv val)).

  Axiom TODO: False.

  Axiom word_to_bv_inj: forall x y, word_to_bv x = word_to_bv y -> x = y.

  Axiom incrN_word_to_bv: forall v, incrN (word_to_bv v) = word_to_bv (word.add (word.of_Z 1) v).

  Set Printing Depth 100000.

  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device increment_wait_state_machine.
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
        cbn -[incrN]. rewrite incrN_word_to_bv.
        eapply BUSY_done_related.
      + (* BUSY_done_related: *)
        cbn. rewrite andb_false_r. cbn. assumption.
      + (* DONE_related: *)
        cbn. rewrite andb_false_r. cbn. assumption.
    - (* state_machine_read_to_device_read: *)
      (* simpler because device.maxRespDelay=1 *)
      unfold device.maxRespDelay, device.runUntilResp, device.state, device.run1, counter_device.
      unfold state_machine.read_step, increment_wait_state_machine in *.
      simp.
      unfold read_step in *.
      destruct r.
      + (* r=VALUE *)
        simp.
        cbn. rewrite andb_false_r. simpl.
        unfold word_to_bv. rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
        simpl. do 3 eexists. ssplit; try reflexivity. eapply IDLE_related.
      + (* r=STATUS *)
        destruct sH.
        * (* sH=IDLE *)
          destruct Hp1. subst. inversion H0. subst.
          cbn. rewrite andb_false_r. simpl. unfold status_value, STATUS_IDLE.
          unfold word_to_bv.
          rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
          do 3 eexists. ssplit; try reflexivity. 2: eapply IDLE_related.
          rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
          destruct idle; reflexivity.
        * (* sH=BUSY *)
          simp.
          destruct Hp1 as [H | H].
          -- (* transition to DONE *)
             destruct H; subst.
             simpl (state_machine.reg_addr _).
             unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_bv, status_value, STATUS_DONE.
             rewrite !word.unsigned_of_Z. unfold word.wrap. simpl.
             inversion H0; subst.
             ++ (* BUSY_related *)
                (* the transition that was used to show that sH is not stuck was a transition
                   from BUSY to DONE returning a done flag, but since the device is still
                   in BUSY state, it will still return the busy flag in this transition,
                   so the transition we use to simulate what happened in the device is a
                   BUSY-to-DONE transition returning a busy flag instead of a done flag *)
                destruct max_cycles_until_done. 1: inversion H3. clear H3.
                exists (word.of_Z 2). (* <- bit #1 (busy) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn -[incrN].
                ssplit; try reflexivity.
                ** simpl. rewrite incrN_word_to_bv. eapply BUSY_done_related.
                ** right. eexists; ssplit; try reflexivity. eapply word.unsigned_inj.
                   rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
                   rewrite !word.unsigned_of_Z. reflexivity.
             ++ (* BUSY_done_related *)
                exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn -[incrN].
                ssplit; try reflexivity.
                ** simpl. eapply DONE_related.
                ** left. split. 2: reflexivity. eapply word.unsigned_inj.
                   rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
                   rewrite !word.unsigned_of_Z. reflexivity.
          -- (* stay BUSY *)
             destruct H as (n & ? & ? & ?); subst.
             simpl (state_machine.reg_addr _).
             unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_bv, status_value, STATUS_BUSY.
             rewrite !word.unsigned_of_Z. unfold word.wrap. simpl.
             inversion H0; subst.
             ++ (* BUSY_related *)
                exists (word.of_Z 2). (* <- bit #1 (busy) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn -[incrN].
                ssplit; try reflexivity.
                ** simpl. rewrite incrN_word_to_bv. eapply BUSY_done_related.
                ** right. eexists; ssplit; try reflexivity. eapply word.unsigned_inj.
                   rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
                   rewrite !word.unsigned_of_Z. reflexivity.
             ++ (* BUSY_done_related *)
                (* the transition that was used to show that sH is not stuck was a transition
                   from BUSY to BUSY returning a busy flag, but since the device already is
                   in done state, it will return a done flag in this transition,
                   so the transition we use to simulate what happened in the device is a
                   BUSY-to-DONE transition returning a done flag instead of a
                   BUSY-to-BUSY transition returning a busy flag. *)
                exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn -[incrN].
                ssplit; try reflexivity.
                ** simpl. eapply DONE_related.
                ** left. split. 2: reflexivity. eapply word.unsigned_inj.
                   rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
                   rewrite !word.unsigned_of_Z. reflexivity.
        * (* sH=DONE *)
          destruct Hp1. subst. inversion H0. subst.
          simpl (state_machine.reg_addr _).
          unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_bv, status_value, STATUS_DONE.
          cbn.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn -[Vec.hd Vec.tl incrN].
          exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
          do 2 eexists.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
          ssplit; try reflexivity.
          ** simpl. eapply DONE_related.
          ** eapply word.unsigned_inj.
             rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
             rewrite !word.unsigned_of_Z. reflexivity.
    - (* state_machine_write_to_device_write: *)
      destruct H as (sH' & ? & ?). subst.
      unfold write_step in H1.
      destruct r. 2: contradiction.
      destruct sH; try contradiction. subst.
      inversion H0. subst.
      cbn.
      unfold word_to_bv.
      rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
      cbn.
      eexists _, _, _. ssplit; try reflexivity. destruct idle; eapply BUSY_related; lia.
    - (* read_step_unique: *)
      cbn in *. unfold read_step in *. simp.
      destruct v; destruct r; try contradiction; simp; try reflexivity.
      destruct Hp1; destruct H0p1; simp; try reflexivity;
        unfold status_value in *; exfalso; ZnWords.
    - (* write_step_unique: *)
      cbn in *. unfold write_step in *. simp. subst. reflexivity.
    - (* initial_state_unique: *)
      cbn in *. subst. reflexivity.
  Qed.

End WithParameters.
