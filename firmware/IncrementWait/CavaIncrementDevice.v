
From Coq Require Import
     Lists.List
     ZArith.ZArith.

Import ListNotations.

From Cava Require Import
     Expr
     Primitives
     Semantics
     Types
     Util.BitArithmetic.

Section Var.
  Import ExprNotations.
  Import PrimitiveNotations.

  Context {var : tvar}.

  Local Open Scope N.

  (* Things that should probably be in cava *)
  Section Cava.
    Definition state_of {i s o} (c : Circuit s i o) := denote_type s.
  End Cava.

  Definition incr
    : Circuit _
              (* Input *)
              [ Bit          (* is_read_req *)
                ; Bit        (* is_write_req *)
                ; BitVec 32  (* req_addr (only relevant if is_read_req or is_write_req) *)
                ; BitVec 32 ](* req_value (only relevant if is_write_req *)
              (* Output *)
              (Bit             (* is_resp *)
                 ** BitVec 32) (* resp (only relevant if is_resp *)
    := {{
      fun is_read_req is_write_req req_addr req_value =>
        (* bit #2 of the address determines if STATUS or VALUE register *)
        let is_value_addr := (req_addr & (`K 1` << 2)) == `K 0` in
        let is_value_write_req := is_value_addr && is_write_req in
        let is_value_read_req := is_value_addr && is_read_req in

        let/delay '(idle, busy, done; value) :=
           if busy == `K 1` then
             (`False`, `K 2`, `False`, value)
           else if busy == `K 2` then
                  (`False`, `K 0`, `True`, value + `K 1`)
                else if done then
                       (is_value_read_req, `K 0`, !is_value_read_req, value)
                     else (* idle *)
                       let busy' := if is_value_write_req then `K 1` else `K 0` in
                       (!is_value_write_req, busy', `False`, req_value)
           initially (false, (0, (false ,0))) : denote_type (Bit ** BitVec 2 ** Bit ** BitVec 32)
        in

        let status := if done then `K 1` else `K 0` in
        let status := (status << 1) | (if busy == `K 0` then `K 0` else `K 1`) in
        let status := (status << 1) | (if idle then `K 1` else `K 0`) in

        let is_resp := is_read_req || is_write_req in
        let resp := if is_value_addr then value else status in
        (is_resp, resp)
       }}.
End Var.

Example sample_trace :=
  Eval compute in simulate incr
                           [ (false,    (false, (111%N, (111%N, tt)))) (* no action *)
                             ; (false,  (true,  (  0%N, ( 15%N, tt)))) (* write VALUE:=15 *)
                             ; (true,   (false, (  4%N, (111%N, tt)))) (* read STATUS *)
                             ; (true,   (false, (  4%N, (111%N, tt)))) (* read STATUS *)
                             ; (true,   (false, (  0%N, (111%N, tt)))) (* read VALUE *)
                           ].

Definition incr_device_step s (input : bool * bool * N * N) : (_ * (bool * N)) :=
  let '(is_read_req, is_write_req, req_addr, req_value) := input in
  step incr s (is_read_req,
               (is_write_req,
                (req_addr, (req_value, tt)))).

Require Import coqutil.Datatypes.List.

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
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

Require Import Cava.Util.Identity.
Require Import Cava.Util.Tactics.

Section WithParameters.
  Instance var : tvar := denote_type.

  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Definition mk_counter_state idle busy done (val : N) : state_of incr :=
    (idle, (busy, (done, val))).

  Global Instance counter_device: device := {|
    device.state := state_of incr;
    device.is_ready_state s := exists val idle, s = mk_counter_state idle 0 false val;
    device.run1 := incr_device_step;
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay := 1;
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.

  Ltac destruct_state s :=
    destruct s as (?idle & ?busy & ?done & ?value).

  Inductive counter_related: IncrementWaitSemantics.state -> state_of incr -> Prop :=
  | IDLE_related: forall val idle,
      (* after reset, all three bools are false, and idle will be set to true *)
      counter_related IDLE (mk_counter_state idle 0 false val)
  | BUSY1_related: forall val ncycles,
      (1 < ncycles)%nat ->
      counter_related (BUSY val ncycles) (mk_counter_state false 1 false (word_to_N val))
  | BUSY2_related: forall val ncycles,
      (0 < ncycles)%nat ->
      counter_related (BUSY val ncycles) (mk_counter_state false 2 false (word_to_N val))
  (* the hardware is already done, but the software hasn't polled it yet to find out,
     so we have to relate a software-BUSY to a hardware-done: *)
  | BUSY_done_related: forall val ncycles,
      counter_related (BUSY val ncycles)
                      (mk_counter_state false 0 true (word_to_N (word.add (word.of_Z 1) val)))
  | DONE_related: forall val,
      counter_related (DONE val) (mk_counter_state false 0 true (word_to_N val)).

  (* This should be in bedrock2.ZnWords. It is use by ZnWords, which is used in
     the two following Lemmas. *)
  Ltac better_lia ::= Zify.zify; Z.to_euclidean_division_equations; Lia.lia.

  Lemma incrN_word_to_bv: forall x,
      ((N.add (word_to_N x) 1) mod 4294967296)%N = word_to_N (word.add (word.of_Z 1) x).
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Lemma Z_word_N: forall x,
      (0 <= x < 2 ^ 32) -> word_to_N (word.of_Z x) = Z.to_N x.
  Proof. intros. unfold word_to_N. ZnWords. Qed.

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
      cbn in H0. simp.
      inversion H; subst; simp;
        (* try rewrite N.land_0_r; *)
        try rewrite Bool.andb_false_r;
        cbn.
      + (* IDLE_related: *)
        apply IDLE_related.
      + (* BUSY1_related: *)
        apply BUSY2_related. Lia.lia.
      + (* BUSY2_related: *)
        rewrite incrN_word_to_bv.
        apply BUSY_done_related.
      + (* BUSY_done_related: *)
        apply BUSY_done_related.
      + (* DONE_related: *)
        apply DONE_related.
    - (* state_machine_read_to_device_read: *)
      (* simpler because device.maxRespDelay=1 *)
      unfold device.maxRespDelay, device.runUntilResp, device.state, device.run1, counter_device.
      unfold state_machine.read_step, increment_wait_state_machine in *.
      simp.
      unfold read_step in *.
      destruct r.
      + (* r=VALUE *)
        simp. cbn. rewrite Z_word_N; try Lia.lia; []. cbn.
        unfold word_to_N.
        (* rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate). *)
        simpl. do 3 eexists. ssplit; try reflexivity.
        eapply IDLE_related.
      + (* r=STATUS *)
        destruct sH.
        * (* sH=IDLE *)
          destruct Hp1. subst. inversion H0. subst.
          cbn. repeat (rewrite Z_word_N; try Lia.lia; []; cbn).
          unfold status_value, STATUS_IDLE, word_to_N.
          (* rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate). *)
          do 3 eexists. ssplit; try reflexivity. 2: eapply IDLE_related.
          rewrite word.unsigned_slu. 2: rewrite word.unsigned_of_Z. 2: reflexivity.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
          destruct idle; reflexivity.
        * (* sH=BUSY *)
          simp. destruct Hp1 as [H | H].
          -- (* transition to DONE *)
             destruct H; subst.
             simpl (state_machine.reg_addr _).
             unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_N, status_value, STATUS_DONE.
             rewrite !word.unsigned_of_Z. unfold word.wrap. simpl.
             inversion H0; subst.
             ++ (* BUSY1_related *)
                destruct max_cycles_until_done. 1: inversion H3. clear H3.
                exists (word.of_Z 2). (* <- bit #1 (busy) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity.
                ** eapply BUSY2_related.
                   instantiate ( 1 := max_cycles_until_done ).
                   inversion H0; subst.
                   Lia.lia.
                ** right. eexists; ssplit; try reflexivity; []. ZnWords.
             ++ (* BUSY2_related *)
                (* the transition that was used to show that sH is not stuck was *)
                (* a transition from BUSY to DONE returning a done flag, but *)
                (* since the device is still in BUSY state, it will still return *)
                (* the busy flag in this transition, so the transition we use to *)
                (* simulate what happened in the device is a BUSY-to-DONE *)
                (* transition returning a busy flag instead of a done flag. *)
               exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                (* destruct max_cycles_until_done. 1: inversion H3. clear H3. *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity; [|].
                ** rewrite incrN_word_to_bv.
                   eapply DONE_related.
                ** left. eexists; ssplit; try reflexivity; []. ZnWords.
             ++ (* BUSY_done_related *)
               exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity; [|].
                ** eapply DONE_related.
                ** left. split; try reflexivity; []. ZnWords.
          -- (* stay BUSY *)
             destruct H as (n & ? & ? & ?); subst.
             simpl (state_machine.reg_addr _).
             unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_N, status_value, STATUS_BUSY.
             rewrite !word.unsigned_of_Z. unfold word.wrap. simpl.
             inversion H0; subst.
             ++ (* BUSY1_related *)
                exists (word.of_Z 2). (* <- bit #1 (busy) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity.
                ** eapply BUSY2_related. instantiate (1 := n).
                   Lia.lia.
                ** right. eexists; ssplit; try reflexivity; []. ZnWords.
             ++ (* BUSY2_related *)
                exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity; [|].
                ** rewrite incrN_word_to_bv.
                   eapply DONE_related.
                ** left. eexists; ssplit; try reflexivity; []. ZnWords.
             ++ (* BUSY_done_related *)
                (* the transition that was used to show that sH is not stuck was *)
                (* a transition from BUSY to BUSY returning a busy flag, but *)
                (* since the device already is in done state, it will return a *)
                (* done flag in this transition, so the transition we use to *)
                (* simulate what happened in the device is a BUSY-to-DONE *)
                (* transition returning a done flag instead of a BUSY-to-BUSY *)
                (* transition returning a busy flag. *)
                exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity.
                ** simpl. eapply DONE_related.
                ** left. split. 2: reflexivity. ZnWords.
        * (* sH=DONE *)
          destruct Hp1. subst. inversion H0. subst.
          simpl (state_machine.reg_addr _).
          unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_N, status_value, STATUS_DONE.
          cbn.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
          exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
          do 2 eexists.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
          ssplit; try reflexivity.
          ** simpl. eapply DONE_related.
          ** ZnWords.
    - (* state_machine_write_to_device_write: *)
      destruct H as (sH' & ? & ?). subst.
      unfold write_step in H1.
      destruct r. 2: contradiction.
      destruct sH; try contradiction. subst.
      inversion H0. subst.
      cbn.
      unfold word_to_N.
      rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
      cbn.
      eexists _, _, _. ssplit; try reflexivity. destruct idle; eapply BUSY1_related; Lia.lia.
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
