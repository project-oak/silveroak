Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Invariant.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.TLUL.
Require Import Cava.Types.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.

Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface coqutil.Word.Properties.

Require Import riscv.Utility.Utility.

Require Import bedrock2.ZnWords.

Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.Incr.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Import ListNotations.

Section WithParameters.
  Instance var : tvar := denote_type.

  Existing Instance Incr.inner_specification.
  Existing Instance Incr.inner_correctness.
  Existing Instance Incr.inner_invariant.

  Existing Instance TLUL.tl_specification.
  Existing Instance TLUL.tlul_invariant.
  Existing Instance TLUL.tlul_adapter_reg_correctness.

  Existing Instance incr_specification.
  Existing Instance incr_invariant.
  Existing Instance incr_correctness.

  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Global Instance counter_device: device := {|
    device.state := denote_type (state_of incr);

    device.is_ready_state s := exists r_regs r_tl r_inner,
        incr_invariant s (RSIdle, r_regs, r_tl, r_inner);

    device.last_d2h '((_, (_, (_, d2h))), _) := d2h;

    device.tl_inflight_ops '((_, (_, (_, d2h))), _) :=
      if d_valid d2h then [d_source d2h] else [];

    device.run1 s i := fst (Semantics.step incr s (i, tt));

    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;

    device.maxRespDelay '((_, (_, (_, d2h))), _) :=
      if a_ready d2h then 0 else 1;
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.


  Inductive counter_related_spec: IncrementWaitSemantics.state -> Incr.repr_state -> Prop :=
  | IDLE_related: counter_related_spec IDLE RSIdle
  | BUSY_related: forall val ncycles count,
      (0 < count <= 2)%nat ->
      (2 < ncycles + count)%nat ->
      counter_related_spec (BUSY val ncycles) (RSBusy (word_to_N val) count)
  (* the hardware is already done, but the software hasn't polled it yet to find out,
     so we have to relate a software-BUSY to a hardware-done: *)
  | BUSY_done_related: forall val ncycles,
      counter_related_spec (BUSY val ncycles) (RSDone (word_to_N (word.add (word.of_Z 1) val)))
  | DONE_related: forall val,
      counter_related_spec (DONE val) (RSDone (word_to_N val)).

  Definition counter_related {invariant : invariant_for incr repr} (sH : IncrementWaitSemantics.state)
             (sL : denote_type (state_of incr)) (inflight_h2ds : list tl_h2d) : Prop :=
    exists r_state r_regs r_tl r_inner,
      inflight_h2ds = [] /\
      counter_related_spec sH r_state /\
      invariant sL (r_state, r_regs, r_tl, r_inner).

  (* This should be in bedrock2.ZnWords. It is use by ZnWords, which is used in
     the two following Lemmas. *)
  Ltac better_lia ::= Zify.zify; Z.to_euclidean_division_equations; lia.

  Lemma incrN_word_to_bv: forall (x : word),
      ((N.add (word_to_N x) 1) mod 4294967296)%N = word_to_N (word.add (word.of_Z 1) x).
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Lemma Z_word_N: forall (x : Z),
      (0 <= x < 2 ^ 32)%Z -> word_to_N (word.of_Z x) = Z.to_N x.
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Lemma N_to_word_word_to_N: forall v, N_to_word (word_to_N v) = v.
  Proof. intros. unfold N_to_word, word_to_N. ZnWords. Qed.

  Ltac use_spec :=
    match goal with
    | Hrun: device.run1 ?sL ?input = ?sL',
            Hinv: incr_invariant ?sL ?repr
      |- _ =>
      assert (Hprec: precondition incr (input, tt) repr);
      [ simplify_spec (incr (var:=var)); simplify_spec (tlul_adapter_reg (reg_count:=2)); simplify_spec (Incr.inner (var:=var));
        simplify_invariant (incr (var:=var));
        cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner));
        destruct_tl_h2d; tlsimpl; logical_simplify; subst;
        ssplit; intros; try discriminate; auto

      | remember (update_repr (c:=incr) (input, tt) repr) as repr' eqn:Erepr';
        (* pose proof (output_correct_pf (c:=incr) (input, tt) sL repr Hinv Hprec) as Hpostc. *)
        pose proof (invariant_preserved_pf (c:=incr) (input, tt) sL repr repr' Erepr' Hinv Hprec) as Hinv';
        unfold device.run1, counter_device in Hrun;
        match type of Hrun with
        | fst ?step = _ =>
          remember step as res eqn:Hstep;
          destruct res as (?sL'' & ?d2h);
          cbn in Hrun; subst sL''; clear Hstep
        end;
        cbn [fst] in Hinv';
        destruct repr' as (((?r_state, ?r_regs), ?r_tl), ?r_inner)]
    end.

  Ltac inversion_rel_spec :=
    match goal with
    | H: counter_related_spec _ _ |- _ => inversion H; subst
    end.

  Ltac simplify_tl_repr :=
    unfold device.maxRespDelay, device.last_d2h, counter_device in *;
    repeat match goal with
    | sL: device.state |- _ =>
      cbn in sL; destruct sL as ((?busy, (?done, (?regs, ?d2h))), (?s_tl, ?s_inner))
    end;
    destruct_tl_h2d; destruct_tl_d2h; tlsimpl; logical_simplify; subst;
    simplify_invariant (incr (var:=var));
    match goal with
    | H: _ = update_repr _ (_, _, ?r_tl, _) |- _ =>
      destruct r_tl; logical_simplify; tlsimpl; subst;
      (* logical_simplify; subst; *)
      cbn in H; rewrite ? Z_word_N in H by lia; cbn in H
    end;
    logical_simplify; subst;
    cbn; rewrite ? Z_word_N by lia; cbn;
    change (Pos.to_nat 1) with 1;
    repeat match goal with
    | H: length ?regs = 2 |- _ =>
      destruct regs as [|? [|? [|]]]; cbn in H; try discriminate H; clear H;
      cbn [nth] in *; subst
    end;
    try discriminate.

  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device increment_wait_state_machine.
  Proof.
    eapply Build_device_implements_state_machine with (device_state_related := counter_related).
    - (* mmioAddrs_match: *)
      reflexivity.
    - (* initial_state_is_ready_state: *)
      intros.
      unfold device.is_ready_state, counter_device, counter_related in *;
        logical_simplify.
      cbn in *; subst.
      inversion_rel_spec; repeat eexists; eassumption.
    - (* initial_states_are_related: *)
      intros.
      cbn in *; logical_simplify; subst.
      unfold counter_related; repeat eexists; [|eassumption].
      apply IDLE_related.
    - (* initial_state_exists: *)
      intros.
      cbn in *; logical_simplify; subst.
      unfold counter_related; repeat eexists; [|eassumption].
      apply IDLE_related.
    - (* nonMMIO_device_step_preserves_state_machine_state: *)
      intros.
      logical_simplify.
      unfold counter_related in *; logical_simplify.
      use_spec. clear Hprec.
      repeat eexists; [|eassumption].
      inversion_rel_spec; simplify_tl_repr;
        destruct d_ready; logical_simplify; subst; try constructor;
          (destruct count as [|[|[|]]]; [exfalso; lia|..|exfalso; lia]);
          rewrite ? incrN_word_to_bv; constructor; lia.

    - (* [state_machine_read_to_device_send_read_or_later] *)
      intros ? ? ? ? ? ? [v [sH'' [Hpow2 Hex_read]]] **.
      rewrite Hpow2. clear Hpow2.
      unfold counter_related in *. cbn in Hex_read. logical_simplify.
      use_spec. clear Hprec.

      destruct_one_match; [destruct_one_match|].
      { (* case 1: device ready, valid response *)
        destruct r.
        - (* [r:=VALUE] *)
          inversion_rel_spec; destruct Hex_read; subst.
          eexists; split; [|cbn; ssplit; try reflexivity].
          + repeat eexists; [|eassumption].
            simplify_tl_repr; constructor.
          + simplify_tl_repr.
            apply N_to_word_word_to_N.
        - (* [r:=STATUS] *)
          inversion_rel_spec.
          + eexists; split; [repeat eexists; [|eassumption]|cbn; ssplit; try reflexivity];
              simplify_tl_repr.
            * constructor.
            * unfold N_to_word, status_value; ZnWords.

          + destruct ncycles as [|]; [exfalso; lia|].
            eexists; split; [repeat eexists; [|eassumption]|cbn; ssplit; try reflexivity];
              simplify_tl_repr.
            * destruct count as [|[|[|]]]; [exfalso; lia|..|exfalso; lia].
              -- apply BUSY_related with (ncycles:=ncycles); lia.
              -- rewrite incrN_word_to_bv; apply BUSY_done_related.
            * right. eexists; ssplit; try reflexivity.
              unfold N_to_word, status_value; ZnWords.

          + eexists; split; [repeat eexists; [|eassumption]|cbn; ssplit; try reflexivity];
              simplify_tl_repr.
            * apply DONE_related.
            * left. split; [|reflexivity].
              unfold N_to_word, status_value; ZnWords.

          + eexists; split; [repeat eexists; [|eassumption]|cbn; ssplit; try reflexivity];
              simplify_tl_repr.
            * apply DONE_related.
            * unfold N_to_word, status_value; ZnWords.
      }

      { (* case 2: device ready, no valid response *)
        exfalso; simplify_tl_repr.
      }

      { (* case 3: device not ready *)
        ssplit.
        - repeat eexists; [|eassumption].
          inversion_rel_spec; simplify_tl_repr;
            rewrite ? incrN_word_to_bv; try (constructor; lia).
          all: destruct count as [|[|[|]]]; [exfalso; lia
                                            |apply BUSY_related with (ncycles:=ncycles); lia
                                            |apply BUSY_done_related
                                            |exfalso; lia].
        - simplify_tl_repr; lia.
      }

    - (* [state_machine_read_to_device_ack_read_or_later] *)
      intros.
      unfold counter_related in *; logical_simplify.
      discriminate.

    - (* [state_machine_write_to_device_send_write_or_later] *)
      intros ? ? ? ? ? ? ? [sH'' [Hpow2 Hex_write]] **.
      rewrite Hpow2. clear Hpow2.
      unfold counter_related in *. logical_simplify.
      use_spec. clear Hprec.
      destruct_one_match; [destruct_one_match|].

      { (* case 1: device ready, valid response *)
        destruct r.
        + (* [r:=VALUE] *)
          inversion_rel_spec; destruct Hex_write; subst.
          eexists; split; [|cbn; ssplit; try reflexivity].
          repeat eexists; [|eassumption].
          simplify_tl_repr; constructor; lia.
        + (* [r:=STATUS] *)
          destruct Hex_write.
      }

      { (* case 2: device ready, no valid response *)
        exfalso; simplify_tl_repr.
      }

      { (* case 3: device not ready *)
        ssplit.
        - repeat eexists; [|eassumption].
          inversion_rel_spec; simplify_tl_repr;
            rewrite ? incrN_word_to_bv; try (constructor; lia).
          all: destruct count as [|[|[|]]]; [exfalso; lia
                                            |apply BUSY_related with (ncycles:=ncycles); lia
                                            |apply BUSY_done_related
                                            |exfalso; lia].
        - simplify_tl_repr; lia.
      }

    - (* [state_machine_write_to_device_ack_write_or_later] *)
      intros.
      unfold counter_related in *; logical_simplify.
      discriminate.

    - (* read_step_unique: *)
      intros. simpl in *. unfold read_step in *. simp.
      destruct v; destruct r; try contradiction; simp; try reflexivity.
      destruct Hp1; destruct H0p1; simp; try reflexivity;
        unfold status_value in *; exfalso; ZnWords.
    - (* write_step_unique: *)
      intros. simpl in *. unfold write_step in *. simp. subst. reflexivity.
    - (* initial_state_unique: *)
      intros. simpl in *. subst. reflexivity.
  Qed.
End WithParameters.
