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
           let '(is_read
                 , is_write
                 , address
                 , write_data
                 ; _write_mask) := req in

           let istate' :=
               if istate == `Busy1` then `Busy2`
               else if istate == `Busy2` then `Done`
                    else if istate == `Done` then
                           if is_read && address == `K 0` then `Idle`
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
    let nop := set_d_ready true tl_h2d_default in
    let read_reg (r : N) :=
        set_a_valid true
        (set_a_opcode Get
        (set_a_size 2%N
        (set_a_address r
        (set_d_ready true tl_h2d_default)))) in
    let write_val (v : N) :=
        set_a_valid true
        (set_a_opcode PutFullData
        (set_a_size 2%N
        (set_a_address 0%N (* value-ref *)
        (set_a_data v
        (set_d_ready true tl_h2d_default))))) in

    simulate incr
             [ (nop, tt)
               ; (read_reg 4, tt) (* status *)
               ; (nop, tt)
               ; (write_val 42, tt)
               ; (nop, tt)
               ; (nop, tt)
               ; (read_reg 4, tt) (* status *)
               ; (nop, tt)
               ; (read_reg 0, tt) (* value *)
               ; (nop, tt)
               ; (read_reg 4, tt) (* status *)
             ]%N.
(* Print sample_trace. *)

Require Import Coq.micromega.Lia.

Require Import riscv.Utility.Utility.

Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.fwd.

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
    device.run1 s i := Semantics.step incr s (i, tt);
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay '((istate, (val, tl_d2h)), tlul_state) h2d :=
      (* if the value register was requested, and we're in state Busy1, it will take one
         more cycle to respond, else we will respond immediately *)
      if ((a_address h2d mod 8 =? 0(*register address=VALUE*))%N && (istate =? 1 (*Busy1*))%N)%bool
      then 1%nat else 0%nat;
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

  Ltac destruct_tlul_adapter_reg_state :=
    match goal with
    | H : N * (N * (N * (bool * (bool * (bool * bool))))) |- _ =>
      destruct H as [?reqid [?reqsz [?rspop [?error [?outstanding [?we_o ?re_o]]]]]]
    end.

  Ltac destruct_consistent_states :=
    match goal with
    | H : consistent_states _ _ |- _ =>
      destruct H as (Hvalid & Hopcode & Hsize & Hsource & Herror & Hready)
    end.

  Lemma N_to_word_word_to_N: forall v, N_to_word (word_to_N v) = v.
  Proof. intros. unfold N_to_word, word_to_N. ZnWords. Qed.

(* TODO move to coqutil *)
Ltac contradictory H :=
  lazymatch type of H with
  | ?x <> ?x => exfalso; apply (H eq_refl)
  | False => case H
  end.
Require Import coqutil.Tactics.autoforward.
Ltac fwd_step ::=
  match goal with
  | H: ?T |- _ => is_destructible_and T; destr_and H
  | H: exists y, _ |- _ => let yf := fresh y in destruct H as [yf H]
  | H: ?x = ?x |- _ => clear H
  | H: True |- _ => clear H
  | H: ?LHS = ?RHS |- _ =>
    let h1 := head_of_app LHS in is_constructor h1;
    let h2 := head_of_app RHS in is_constructor h2;
    (* if not eq, H is a contradiction, but we don't want to change the number
       of open goals in this tactic *)
    constr_eq h1 h2;
    (* we don't use `inversion H` or `injection H` because they unfold definitions *)
    inv_rec LHS RHS;
    clear H
  | E: ?x = ?RHS |- context[match ?x with _ => _ end] =>
    let h := head_of_app RHS in is_constructor h; rewrite E in *
  | H: context[match ?x with _ => _ end], E: ?x = ?RHS |- _ =>
    let h := head_of_app RHS in is_constructor h; rewrite E in *
  | H: context[match ?x with _ => _ end] |- _ =>
    (* note: recursive invocation of fwd_step for contradictory cases *)
    destr x; try solve [repeat fwd_step; contradictory H]; []
  | H: _ |- _ => autoforward with typeclass_instances in H
  | |- _ => progress subst
  | |- _ => progress fwd_rewrites
  end.

  Axiom TODO: False.

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
      destruct_tl_h2d. simpl in H. subst.
      cbn in H1.
      repeat (destruct_pair_let_hyp;
              repeat (destruct_pair_equal_hyp; subst; cbn [fst snd])).
      inversion H0; subst;
        try (rewrite incrN_word_to_bv);
        try (constructor; try lia; simpl; boolsimpl; ssplit; reflexivity).
    - (* state_machine_read_to_device_read_or_later: *)
      case TODO.
      (*
      cbn [counter_device device.state device.is_ready_state device.run1 device.addr_range_start
           device.addr_range_pastend device.maxRespDelay] in *.
      cbn [increment_wait_state_machine
             state_machine.state
             state_machine.register
             state_machine.is_initial_state
             state_machine.read_step
             state_machine.write_step
             state_machine.reg_addr
             state_machine.isMMIOAddr] in *.
      simpl in sL. destruct sL as ((istate & value & tl_d2h) & tlul_state).
      destruct_tl_d2h. destruct_tlul_adapter_reg_state.
      destruct H as [v [sH' [Hbytes H]]]. rewrite Hbytes.
      tlsimpl.
      destruct r; simp.
      + (* r=VALUE *)
        destruct_tl_h2d.
        cbn in *. subst.

        destruct_consistent_states. subst.
        destruct outstanding; cbn in H1|-*; fwd.


          eexists _, _, _; ssplit; try reflexivity; cbn; rewrite Z_word_N by lia;
            try (eapply IDLE_related; unfold consistent_states; ssplit; reflexivity);
            try (apply N_to_word_word_to_N).
      + (* r=STATUS *)
        destruct sH; [| |].
        * (* sH=IDLE *)
          inversion H0. subst.
          destruct_consistent_states. subst. cbn.
          repeat (rewrite Z_word_N by lia; cbn).
          unfold status_value, STATUS_IDLE, N_to_word, word_to_N.
          destruct outstanding; eexists _, _, _; ssplit; try reflexivity;
              try (apply IDLE_related; simpl; ssplit; reflexivity);
              try (simpl; unfold N_to_word; ZnWords).
        * (* sH=BUSY *)
          simpl.
          unfold STATUS_ADDR, INCR_BASE_ADDR, N_to_word, word_to_N, status_value, STATUS_BUSY.
          rewrite word.unsigned_of_Z. unfold word.wrap.
          inversion H0; subst; [| |].
          -- (* BUSY1_related *)
            destruct outstanding; eexists _, _, _; simpl; [|].
            ++ ssplit; try reflexivity; [|].
               ** rewrite incrN_word_to_bv.
                  apply BUSY_done_related; unfold consistent_states; ssplit; reflexivity.
               ** right. eexists. ssplit; try reflexivity; [|].
                  --- apply Nat.pred_inj; try lia. rewrite Nat.pred_succ. reflexivity.
                  --- simpl. ZnWords.
            ++ ssplit; try reflexivity; [|].
               ** apply BUSY2_related. 1: shelve. unfold consistent_states. ssplit; reflexivity.
               ** right. eexists. ssplit; try reflexivity; [|].
                  --- apply Nat.pred_inj; try lia. rewrite Nat.pred_succ. reflexivity.
                  --- simpl. ZnWords.
                      Unshelve. lia.
          -- (* BUSY2_related *)
            destruct outstanding; eexists _, _, _; simpl; [|].
            ++ ssplit; try reflexivity; [|].
              ** rewrite incrN_word_to_bv.
                 apply DONE_related; unfold consistent_states; ssplit; reflexivity.
              ** left. simpl. ssplit; try reflexivity. ZnWords.
            ++ ssplit; try reflexivity; [|].
              ** rewrite incrN_word_to_bv.
                 apply BUSY_done_related; unfold consistent_states; ssplit; reflexivity.
              ** right. eexists. ssplit; try reflexivity; [|].
                 --- apply Nat.pred_inj; try lia. rewrite Nat.pred_succ. reflexivity.
                 --- simpl. ZnWords.
          -- (* BUSY_done_related *)
            (* the transition that was used to show that sH is not stuck was *)
            (* a transition from BUSY to BUSY returning a busy flag, but *)
            (* since the device already is in done state, it will return a *)
            (* done flag in this transition, so the transition we use to *)
            (* simulate what happened in the device is a BUSY-to-DONE *)
            (* transition returning a done flag instead of a BUSY-to-BUSY *)
            (* transition returning a busy flag. *)
            destruct outstanding; eexists _, _, _; boolsimpl; simpl;
              ssplit; try reflexivity;
                try (apply DONE_related; unfold consistent_states; ssplit; reflexivity);
                try (left; split; try reflexivity; simpl; ZnWords).
        * (* sH=DONE *)
          simpl.
          unfold STATUS_ADDR, INCR_BASE_ADDR, N_to_word, word_to_N, status_value, STATUS_BUSY.
          rewrite !word.unsigned_of_Z. unfold word.wrap.
          inversion H0. subst.
          destruct outstanding; eexists _, _, _; boolsimpl; simpl;
            ssplit; try reflexivity;
              try (eapply DONE_related; unfold consistent_states; ssplit; reflexivity);
              try (simpl; ZnWords).
      *)
    - (* state_machine_write_to_device_write_or_later: *)
      case TODO.
      (*
      destruct H as (sH' & ? & ?). subst.
      unfold write_step in H1.
      destruct r. 2: contradiction.
      destruct sH; try contradiction. subst.
      inversion H0. simpl in tl_d2h. simpl in tlul_state.
      destruct_tl_d2h. destruct_tlul_adapter_reg_state. subst. cbn.
      unfold word_to_N.
      rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
      destruct outstanding; boolsimpl; simpl;
        eexists _, _, _; ssplit; try reflexivity; try assumption; apply BUSY1_related;
          try lia;
          try (unfold consistent_states; ssplit; reflexivity).
      *)
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
