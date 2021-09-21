From Coq Require Import
     Lists.List
     ZArith.ZArith.

Import ListNotations.

From Cava Require Import
     Expr
     Primitives
     Semantics
     TLUL
     Types
     Util.BitArithmetic.

Section Var.
  Import ExprNotations.
  Import PrimitiveNotations.

  Local Open Scope N.

  Context {var : tvar}.

  Definition incr_state := BitVec 2.
  Definition Idle       := Constant incr_state 0.
  Definition Busy1      := Constant incr_state 1.
  Definition Busy2      := Constant incr_state 2.
  Definition Done       := Constant incr_state 3.

  Definition incr
    : Circuit _ [tl_h2d_t] tl_d2h_t
    := {{
      fun tl_h2d =>
        (* Destruct and reassemble tl_h2d with a_address that matches the
           tlul_adapter_reg interface. *)
        let '(a_valid
              , a_opcode
              , a_param
              , a_size
              , a_source
              , a_address
              , a_mask
              , a_data
              , a_user
              ; d_ready) := tl_h2d in
        (* Bit #2 of the address determines which register is being accessed
           (STATUS or VALUE). Zero out the other bits. *)
        let a_address := a_address & (`K 1` << 2) in
        let tl_h2d := (a_valid
                       , a_opcode
                       , a_param
                       , a_size
                       , a_source
                       , a_address
                       , a_mask
                       , a_data
                       , a_user
                       , d_ready) in

        let/delay '(istate, value; tl_d2h) :=
           let '(_, _, _, _, _, _, _, _, _; a_ready) := tl_d2h in

           (* Compute the value of the status register *)
           let status :=
               if istate == `Done` then `K 4`
               else if istate == `Busy1` || istate == `Busy2` then `K 2`
                    else (* istate == `Idle` *) `K 1` in

           (* Handle the input:
              - a_opcode = Get: the adapter will do all the work;
              - a_opcode = PutFullData: further handling is needed, the adapter
                will output more info to req. *)
           let '(tl_d2h'; req) := `tlul_adapter_reg` tl_h2d (value :> status :> []) in

           let '(is_write
                 , _write_addr
                 , write_data
                 ; _write_mask) := req in

           let is_value_read_req := a_valid
                                    && a_ready
                                    && a_opcode == `Get`
                                    && a_address == `K 0` in

           let istate' :=
               if istate == `Busy1` then `Busy2`
               else if istate == `Busy2` then `Done`
                    else if istate == `Done` then
                           if is_value_read_req then `Idle`
                           else `Done`
                         else (* istate == `Idle` *)
                           if is_write then `Busy1`
                           else `Idle` in

           let value' :=
               if istate == `Busy2` then value + `K 1`
               else if istate == `Idle` then write_data
                    else value in

           (istate', value', tl_d2h')
             initially (0,
                        (0,
                         (false, (0, (0, (0, (0, (0, (0, (0, (false, false)))))))))))
           : denote_type (incr_state ** BitVec 32 ** tl_d2h_t)
        in

        tl_d2h
       }}.
End Var.

Example sample_trace :=
  Eval compute in
    let nop :=
        ((false,        (* a_valid   *)
          (0,           (* a_opcode  *)
           (0,          (* a_param   *)
            (0,         (* a_size    *)
             (0,        (* a_source  *)
              (0,       (* a_address *)
               (0,      (* a_mask    *)
                (0,     (* a_data    *)
                 (0,    (* a_user    *)
                  (true (* d_ready   *)
         )))))))))), tt)%N in

    let read_reg (r : N) :=
        ((true,         (* a_valid   *)
          (4,           (* a_opcode  Get *)
           (0,          (* a_param   *)
            (0,         (* a_size    *)
             (0,        (* a_source  *)
              (r,       (* a_address *)
               (0,      (* a_mask    *)
                (0,     (* a_data    *)
                 (0,    (* a_user    *)
                  (true (* d_ready   *)
         )))))))))), tt)%N in

    let write_val (v : N) :=
        ((true,         (* a_valid   *)
          (0,           (* a_opcode  PutFullData *)
           (0,          (* a_param   *)
            (0,         (* a_size    *)
             (0,        (* a_source  *)
              (0,       (* a_address value-reg *)
               (0,      (* a_mask    *)
                (v,     (* a_data    *)
                 (0,    (* a_user    *)
                  (true (* d_ready   *)
         )))))))))), tt)%N in

    simulate incr
             [ nop
               ; read_reg 4 (* status *)
               ; nop
               ; write_val 42
               ; nop
               ; nop
               ; read_reg 4 (* status *)
               ; nop
               ; read_reg 0 (* value *)
               ; nop
               ; read_reg 4 (* status *)
             ]%N.
Print sample_trace.

(* Require Import Coq.ZArith.ZArith. Open Scope Z_scope. *)

From Coq Require Import Lia.

Require Import riscv.Utility.Utility.

Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.

Require Import bedrock2.ZnWords.

Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Require Import Cava.Util.Tactics.

Section WithParameters.
  Instance var : tvar := denote_type.

  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Definition incr_device_step (s : denote_type (state_of incr))
             '((is_read_req, is_write_req, req_addr, req_value) : (bool * bool * N * N))
    : denote_type (state_of incr) * (bool * N) :=
    let input := ((is_read_req || is_write_req,     (* a_valid   *)
                   (if is_read_req then 4 else 0, (* a_opcode  *)
                    (0,                           (* a_param   *)
                     (0,                          (* a_size    *)
                      (0,                         (* a_source  *)
                       (req_addr,                 (* a_address *)
                        (0,                       (* a_mask    *)
                         (req_value,              (* a_data    *)
                          (0,                     (* a_user    *)
                           true                   (* d_ready   *)
                  ))))))))), tt)%N%bool in
    let '(s', output) := Semantics.step incr s input in
    let '(d_valid,
          (_d_opcode,
           (_d_param,
            (_d_size,
             (_d_source,
              (_d_sink,
               (d_data,
                (_d_user,
                 (_d_error,
                  _a_ready))))))))) := output in
    (s', (d_valid, d_data)).

  Definition consistent_states
             '((reqid, (reqsz, (rspop, (error, (outstanding, (_we_o, _re_o))))))
               : denote_type (state_of (tlul_adapter_reg (reg_count := 2))))
             '((d_valid, (d_opcode, (d_param, (d_size, (d_source, (d_sink, (d_data, (d_user, (d_error, a_ready)))))))))
               : denote_type tl_d2h_t)
    : Prop :=
      d_valid = outstanding /\
      d_opcode = rspop /\
      (* d_param = 0 /\ *)
      d_size = reqsz /\
      d_source = reqid /\
      (* d_sink = 0 /\ *)
      (* d_data = ?? *)
      (* d_user = 0 /\ *)
      d_error = error /\
      a_ready = negb outstanding.

  Definition mk_counter_state (istate : N) (val : N) tl_d2h tlul_state
    : denote_type (state_of incr) :=
    ((istate, (val, tl_d2h)), tlul_state).

  Global Instance counter_device: device := {|
    device.state := denote_type (state_of incr);
    device.is_ready_state s := exists val tl_d2h tlul_state,
        consistent_states tlul_state tl_d2h
        /\ s = mk_counter_state 0 val tl_d2h tlul_state;
    device.run1 := incr_device_step;
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay := 1;
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.

  Inductive counter_related: IncrementWaitSemantics.state -> denote_type (state_of incr) -> Prop :=
  | IDLE_related: forall val tl_d2h tlul_state,
      consistent_states tlul_state tl_d2h ->
      counter_related IDLE (mk_counter_state 0 val tl_d2h tlul_state)
  | BUSY1_related: forall val tl_d2h tlul_state ncycles,
      (1 < ncycles)%nat ->
      consistent_states tlul_state tl_d2h ->
      counter_related (BUSY val ncycles) (mk_counter_state 1 (word_to_N val) tl_d2h tlul_state)
  | BUSY2_related: forall val tl_d2h tlul_state ncycles,
      (0 < ncycles)%nat ->
      consistent_states tlul_state tl_d2h ->
      counter_related (BUSY val ncycles) (mk_counter_state 2 (word_to_N val) tl_d2h tlul_state)
  (* the hardware is already done, but the software hasn't polled it yet to find out,
     so we have to relate a software-BUSY to a hardware-done: *)
  | BUSY_done_related: forall val tl_d2h tlul_state ncycles,
      consistent_states tlul_state tl_d2h ->
      counter_related (BUSY val ncycles)
                      (mk_counter_state 3 (word_to_N (word.add (word.of_Z 1) val)) tl_d2h tlul_state)
  | DONE_related: forall val tl_d2h tlul_state,
      consistent_states tlul_state tl_d2h ->
      counter_related (DONE val) (mk_counter_state 3 (word_to_N val) tl_d2h tlul_state).

  (* This should be in bedrock2.ZnWords. It is use by ZnWords, which is used in
     the two following Lemmas. *)
  Ltac better_lia ::= Zify.zify; Z.to_euclidean_division_equations; lia.

  Lemma incrN_word_to_bv: forall (x : word),
      ((N.add (word_to_N x) 1) mod 4294967296)%N = word_to_N (word.add (word.of_Z 1) x).
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Lemma Z_word_N: forall (x : Z),
      (0 <= x < 2 ^ 32)%Z -> word_to_N (word.of_Z x) = Z.to_N x.
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Set Printing Depth 100000.

  Ltac destruct_pair_let_hyp :=
    match goal with
    | H: context [ match ?p with
                   | pair _ _ => _
                   end ] |- _ =>
      destruct p as [?p0 ?p1] eqn:?H0
    end.

  Ltac destruct_pair_equal_hyp :=
    match goal with
    | H: context [ (?l0, ?l1) = (?r0, ?r1) ] |- _ =>
      eapply pair_equal_spec in H; destruct H as [?H0 ?H1]
    end.

  Ltac destruct_tl_d2h :=
    match goal with
    | H : bool * (N * (N * (N * (N * (N * (N * (N * (bool * bool)))))))) |- _ =>
      destruct H as [d_valid [d_opcode [d_param [d_size [d_source [d_sink [d_data [d_user [d_error a_ready]]]]]]]]]
    end.

  Ltac destruct_tlul_adapter_reg_state :=
    match goal with
    | H : N * (N * (N * (bool * (bool * (bool * bool))))) |- _ =>
      destruct H as [reqid [reqsz [rspop [error [outstanding [we_o re_o]]]]]]
    end.

  Ltac destruct_consistent_states :=
    match goal with
    | H : consistent_states _ _ |- _ =>
      destruct H as (Hvalid & Hopcode & Hsize & Hsource & Herror & Hready)
    end.

  (* Set Printing All. *)
  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device increment_wait_state_machine.
  Proof.
    eapply Build_device_implements_state_machine with (device_state_related := counter_related);
      intros.
    - (* mmioAddrs_match: *)
      reflexivity.
    - (* initial_state_is_ready_state: *)
      simpl in *. subst. inversion H0. subst. eexists _, _, _. eauto.
    - (* initial_states_are_related: *)
      simpl in *. destruct H0 as (val & tl_d2h & tlul_state & H0 & H1). subst.
      eauto using IDLE_related.
    - (* initial_state_exists: *)
      simpl in *. destruct H as (val & tl_d2h & tlul_state & H0 & H1). subst.
      eauto using IDLE_related.
    - (* nonMMIO_device_step_preserves_state_machine_state: *)
      simpl in sL1, sL2.
      cbn in H0.
      repeat destruct_pair_let_hyp. (* <-- very slow, but faster then simp *)
      repeat (destruct_pair_equal_hyp; subst; cbn).
      inversion H; subst;
        try (rewrite incrN_word_to_bv);
        try (constructor; try lia; simpl; boolsimpl; ssplit; reflexivity).
    - (* state_machine_read_to_device_read: *)
      (* simpler because device.maxRespDelay=1 *)
      unfold device.maxRespDelay, device.runUntilResp, device.state, device.run1, counter_device.
      unfold state_machine.read_step, increment_wait_state_machine, read_step in *.
      simp.
      simpl in sL. destruct sL as ((istate & value & tl_d2h) & tlul_state).
      destruct_tl_d2h. destruct_tlul_adapter_reg_state.
      destruct r.
      + (* r=VALUE *)
        simp.
        destruct_consistent_states. subst.
        repeat (rewrite Z_word_N by lia; cbn).
        destruct outstanding; [|];
          eexists _, _, _; ssplit; try reflexivity;
            eapply IDLE_related; unfold consistent_states; ssplit; reflexivity.
      + (* r=STATUS *)
        destruct sH.
        * (* sH=IDLE *)
          inversion H0. subst.
          destruct_consistent_states. subst. cbn.
          repeat (rewrite Z_word_N by lia; cbn).
          unfold status_value, STATUS_IDLE, word_to_N.
          destruct outstanding; eexists _, _, _.
          -- ssplit; try reflexivity.
             ++ rewrite word.unsigned_slu by ZnWords.
                rewrite !word.unsigned_of_Z.
                simpl. reflexivity.
             ++ apply IDLE_related. simpl. ssplit; reflexivity.
          -- ssplit; try reflexivity; [|].
             ++ rewrite word.unsigned_slu by ZnWords.
                rewrite !word.unsigned_of_Z.
                simpl. reflexivity.
             ++ apply IDLE_related. simpl. ssplit; reflexivity.
        * (* sH=BUSY *)
          simpl.
          unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_N, status_value, STATUS_BUSY.
          rewrite word.unsigned_of_Z. unfold word.wrap.
          inversion H0; subst.
          -- (* BUSY1_related *)
            exists (word.of_Z 2). (* <- bit #1 (busy) is set, all others are 0 *)
            destruct outstanding; simpl; eexists _, _.
            ++ rewrite word.unsigned_of_Z. unfold word.wrap. simpl.
               ssplit; try reflexivity; [|].
               ** rewrite incrN_word_to_bv.
                  apply BUSY_done_related; unfold consistent_states; ssplit; reflexivity.
               ** right. exists (Nat.pred max_cycles_until_done). ssplit.
                  --- lia.
                  --- ZnWords.
                  --- reflexivity.
            ++ rewrite word.unsigned_of_Z. unfold word.wrap. simpl.
               ssplit; try reflexivity; [|].
               ** apply BUSY2_related. 1: shelve. unfold consistent_states. ssplit; reflexivity.
               ** right. exists (Nat.pred max_cycles_until_done). ssplit.
                  --- lia.
                  --- ZnWords.
                  --- reflexivity.
                      Unshelve. lia.
          -- (* BUSY2_related *)
            destruct outstanding; simpl.
            ++ (* outstanding = true *)
              exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
              eexists _, _.
              rewrite word.unsigned_of_Z. unfold word.wrap.
              simpl. ssplit; try reflexivity; [|].
              ** rewrite incrN_word_to_bv.
                 apply DONE_related; unfold consistent_states; ssplit; reflexivity.
              ** left. ssplit; try reflexivity. ZnWords.
            ++ (* outstanding = false *)
              exists (word.of_Z 2). (* <- bit #1 (busy) is set, all others are 0 *)
              eexists _, _.
              rewrite word.unsigned_of_Z. unfold word.wrap. simpl.
              ssplit; try reflexivity; [|].
              ** rewrite incrN_word_to_bv.
                 apply BUSY_done_related; unfold consistent_states; ssplit; reflexivity.
              ** right. exists (Nat.pred max_cycles_until_done). ssplit.
                 --- lia.
                 --- ZnWords.
                 --- reflexivity.
          -- (* BUSY_done_related *)
            (* the transition that was used to show that sH is not stuck was *)
            (* a transition from BUSY to BUSY returning a busy flag, but *)
            (* since the device already is in done state, it will return a *)
            (* done flag in this transition, so the transition we use to *)
            (* simulate what happened in the device is a BUSY-to-DONE *)
            (* transition returning a done flag instead of a BUSY-to-BUSY *)
            (* transition returning a busy flag. *)
            exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
            destruct outstanding; boolsimpl; simpl;
              eexists _, _.
            ++ rewrite word.unsigned_of_Z. unfold word.wrap. cbn.
               ssplit; try reflexivity; [|].
               ** apply DONE_related. unfold consistent_states; ssplit; reflexivity.
               ** left. split. 2: reflexivity. ZnWords.
            ++ rewrite word.unsigned_of_Z. unfold word.wrap. cbn.
               ssplit; try reflexivity; [|].
               ** apply DONE_related. unfold consistent_states; ssplit; reflexivity.
               ** left. split. 2: reflexivity. ZnWords.
        * (* sH=DONE *)
          simpl.
          unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_N, status_value, STATUS_BUSY.
          rewrite !word.unsigned_of_Z. unfold word.wrap.
          inversion H0. subst.
          exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
          rewrite word.unsigned_of_Z. unfold word.wrap. cbn.
          destruct outstanding; eexists _, _; boolsimpl; simpl.
          -- ssplit; try reflexivity; [|]. 2: ZnWords.
             eapply DONE_related; unfold consistent_states; ssplit; reflexivity.
          -- ssplit; try reflexivity; [|]. 2: ZnWords.
             eapply DONE_related; unfold consistent_states; ssplit; reflexivity.
    - (* state_machine_write_to_device_write: *)
      destruct H as (sH' & ? & ?). subst.
      unfold write_step in H1.
      destruct r. 2: contradiction.
      destruct sH; try contradiction. subst.
      inversion H0. simpl in tl_d2h. simpl in tlul_state.
      destruct_tl_d2h. destruct_tlul_adapter_reg_state. subst. cbn.
      unfold word_to_N.
      rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
      destruct outstanding; boolsimpl; simpl; [|].
      * eexists _, _, _. ssplit; try reflexivity; [].
        apply BUSY1_related. 1: lia.
        unfold consistent_states; ssplit; reflexivity.
      * eexists _, _, _. ssplit; try reflexivity; [].
        apply BUSY1_related. 1: lia.
        unfold consistent_states; ssplit; reflexivity.
    - (* read_step_unique: *)
      simpl in *. unfold read_step in *. simp.
      destruct v; destruct r; try contradiction; simp; try reflexivity.
      destruct Hp1; destruct H0p1; simp; try reflexivity;
        unfold status_value in *; exfalso; ZnWords.
    - (* write_step_unique: *)
      simpl in *. unfold write_step in *. simp. subst. reflexivity.
    - (* initial_state_unique: *)
      simpl in *. subst. reflexivity.
  Qed.
End WithParameters.
