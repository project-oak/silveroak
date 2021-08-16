Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.Loops.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.letexists.
Require Import coqutil.Z.Lia.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.WhileProperties.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.Uart.UartSemantics.
Require Import Bedrock2Experiments.Uart.Uart.
Require Import Bedrock2Experiments.Uart.Constants.
Require Import Bedrock2Experiments.LibBase.AbsMMIOProperties.
Require Import Bedrock2Experiments.LibBase.BitfieldProperties.
Require Import Bedrock2Experiments.LibBase.MMIOLabels.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(* bedrock2.ProgramLogic does cbv, which unfolds the getters of uart_constants,
   resulting in large ugly ASTs *)
Ltac normalize_body_of_function f ::= Tactics.rdelta.rdelta f.

Section Proofs.
  Context {word: word.word 32} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {circuit_spec : circuit_behavior}.

  (* Plug in the right state machine parameters; typeclass inference struggles here *)
  Local Notation execution := (execution (M:=uart_state_machine)).

  (***** General-purpose lemmas/tactics and setup *****)

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Ltac solve_status_valid :=
      cbv [is_flag_set]; boolsimpl;
      repeat lazymatch goal with
             | |- (_ && _)%bool = true => apply Bool.andb_true_iff; split
             | |- negb _ = true => apply Bool.negb_true_iff
             end;
      rewrite word.unsigned_eqb;
      unfold UART_STATUS_TXEMPTY_BIT;
      unfold UART_STATUS_TXIDLE_BIT;
      unfold UART_STATUS_TXFULL_BIT;
      first [ apply Z.eqb_eq | apply Z.eqb_neq ];
      push_unsigned;
      repeat rewrite Z.shiftl_1_l;
      repeat rewrite word.wrap_small;
      simpl;
      lia.

  Ltac separate_flags :=
    repeat lazymatch goal with
           | H: (_ && _)%bool = true |- _ =>
               apply andb_prop in H; logical_simplify
           end.


  Lemma status_read_always_ok s :
    exists val s', read_step s STATUS val s'.
  Proof.
    destruct s; unfold read_step; cbn [read_step];
    cbv [status_matches_state].
    { (* s = IDLE => s' = IDLE *)
      exists (word.or (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXEMPTY_BIT))
                      (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXIDLE_BIT))).
      exists IDLE.
      split; [ solve_status_valid | reflexivity ].
    }
    { (* s = BUSY n *)
      destruct (Nat.eqb txlvl 0)%bool eqn:H.
      { (* s = BUSY O => s' = IDLE *)
        apply Nat.eqb_eq in H. subst.
        exists (word.or (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXEMPTY_BIT))
                        (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXIDLE_BIT))).
        exists IDLE.
        split; [ solve_status_valid | left; reflexivity ].
      }
      { (* s = BUSY txlvl where txlvl <> 0 *)
        exists (word.or (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXEMPTY_BIT))
                        (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXIDLE_BIT))).
        exists IDLE.
        split; [ solve_status_valid | left; reflexivity ].
      }
    }
  Qed.

  Lemma execution_unique (t : trace) s1 s2 :
    execution t s1 ->
    execution t s2 ->
    s1 = s2.
  Proof.
    eapply StateMachineProperties.execution_unique; intros.
    all:cbn [state_machine.is_initial_state state_machine.read_step state_machine.write_step
             uart_state_machine] in *; subst; try reflexivity.
    all:cbv [write_step read_step] in *; subst.
    all:repeat destruct_one_match_hyp; try congruence.
    all:logical_simplify; subst.
    all:lazymatch goal with
        | H : False |- _ => contradiction H
        | H1 : ?x = Some ?a, H2 : ?x = Some ?b |- _ =>
          rewrite H1 in H2; inversion H2; clear H2; subst
        | _ => idtac
        end;
    try lazymatch goal with
    | H: [?a] = [?b] |- _ => inversion H; subst a
    end.
    all:try reflexivity.
    all:cbv [status_matches_state] in *.

    all:lazymatch goal with
        | H0: _ \/ _, H1: _ \/ _ |- _ => destruct H0; destruct H1; logical_simplify; subst;
            try reflexivity
    end.
    {
      separate_flags.
      lazymatch goal with
      | H0: is_flag_set _ ?z = true, H1: negb (is_flag_set _ ?z) = true |- _ => rewrite H0 in H1;
          discriminate
      end.
    }
    {
      destruct x.
      {
        simpl in *.
        separate_flags.
        lazymatch goal with
        | H0: is_flag_set _ ?z = true, H1: negb (is_flag_set _ ?z) = true |- _ => rewrite H0 in H1;
            discriminate
        end.
      }
      {
        simpl in *.
        separate_flags.
        lazymatch goal with
        | H0: is_flag_set _ ?z = true, H1: negb (is_flag_set _ ?z) = true |- _ => rewrite H0 in H1;
            discriminate
        end.
      }
    }
    {
      lazymatch goal with
      | H: S _ = S _ |- _ => apply Nat.succ_inj in H; subst
      end.
      reflexivity.
    }
  Qed.

  Lemma reg_is_status :
    forall r,
    reg_addr r = word.of_Z (TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET) ->
    r = STATUS.
  Proof.
    intros.
    destruct r; apply reg_addr_unique; eauto.
  Qed.

  Lemma reg_is_wdata :
    forall r,
    reg_addr r = word.of_Z (TOP_EARLGREY_UART0_BASE_ADDR + UART_WDATA_REG_OFFSET) ->
    r = WDATA.
  Proof.
    intros.
    destruct r; apply reg_addr_unique; eauto.
  Qed.

  Lemma reg_is_ctrl :
    forall r,
    reg_addr r = word.of_Z (TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET) ->
    r = CTRL.
  Proof.
    intros.
    destruct r; apply reg_addr_unique; eauto.
  Qed.

  Local Ltac infer_reg_using_addr :=
    let base := TOP_EARLGREY_UART0_BASE_ADDR in
    lazymatch goal with
      | H: reg_addr _ = _ |- _ => rewrite <- word.ring_morph_add in H
      end;
    lazymatch goal with
    | H: reg_addr _ = word.of_Z (base + UART_STATUS_REG_OFFSET) |- _ => apply reg_is_status in H; subst
    | H: reg_addr _ = word.of_Z (base + UART_CTRL_REG_OFFSET) |- _ => apply reg_is_ctrl in H; subst
    | H: reg_addr _ = word.of_Z (base + UART_WDATA_REG_OFFSET) |- _ => apply reg_is_wdata in H; subst
    end.


  (***** Proofs for specific functions *****)
  Global Instance spec_of_uart_tx_full : spec_of "b2_uart_tx_full" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) (s : state),
      (* no special requirements of the memory *)
      R m ->
      (* no constraints on current state *)
      execution tr s ->
      call function_env uart_tx_full tr m []
        (fun tr' m' rets =>
          exists (status out : word) (s' : state),
            (* the new state matches the new trace *)
            execution tr' s'
            (* ...and there exists a single valid status-read step between
               the old and new state, and the read result was [status] *)
            /\ read_step s STATUS status s'
            (* ...and all the same properties as before hold on the memory *)
            /\ R m'
            (* ...and there is one output value *)
            /\ rets = [out]
            (* ...and the output value is one if and only if the
               txfull flag is set *)
            /\ word.eqb out (word.of_Z 0)
              = negb (is_flag_set status UART_STATUS_TXFULL_BIT)).
  Lemma uart_tx_full_correct :
    program_logic_goal_for_function! uart_tx_full.
  Proof.
    (* TODO the proof is almost identical to one for uart_tx_idle_correct, but
       it is hard to generalize the proof becausae it calls the function twice *)
    repeat straightline.
    pose proof status_read_always_ok s as Hstat.
    destruct Hstat as (x & s' & Hstat).
    straightline_call; ssplit.
    { instantiate (1 := STATUS). apply word.ring_morph_add. }
    { cbv [state_machine.read_step uart_state_machine read_step] in *. eauto. }
    { eauto. }
    { repeat straightline.
      straightline_call; eauto.
      repeat straightline.
      (* keep "execution a x" for later eassumption *)
      lazymatch goal with
      | H0 : execution tr _, H1: execution ?a _ |-  context [?tr] => rename H0 into Hexec; rename H1 into Hexec'
      end.
      pose proof Hexec' as HH.
      simpl in Hexec'.
      destruct Hexec' as (x' & Hexec').
      destruct Hexec'.
      replace s with x' in *.
      2:{ eapply execution_unique; eauto. }
      lazymatch goal with
      | H: step _ _ _ _ _ |- _ => unfold step in H; simpl in H
      end.
      logical_simplify.
      infer_reg_using_addr.
      do 3 eexists; ssplit; eauto.
      lazymatch goal with
      | H: [_] = [_] |- _ => inversion H; subst
      end.
      unfold UART_STATUS_TXFULL_BIT in *.
      apply is_flag_set_and_select_bits.
      + cbv. reflexivity.
      + split; try lia.
    }
  Qed.


  Global Instance spec_of_uart_tx_idle : spec_of "b2_uart_tx_idle" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) (s : state),
      (* no special requirements of the memory *)
      R m ->
      (* no constraints on current state *)
      execution tr s ->
      call function_env uart_tx_idle tr m []
        (fun tr' m' rets =>
          exists (status out : word) (s' : state),
            (* the new state matches the new trace *)
            execution tr' s'
            (* ...and there exists a single valid status-read step between
               the old and new state, and the read result was [status] *)
            /\ read_step s STATUS status s'
            (* ...and all the same properties as before hold on the memory *)
            /\ R m'
            (* ...and there is one output value *)
            /\ rets = [out]
            (* ...and the output value is one if and only if the
               txidle flag is set *)
            /\ word.eqb out (word.of_Z 0)
              = negb (is_flag_set status UART_STATUS_TXIDLE_BIT)).
  Lemma uart_tx_idle_correct :
    program_logic_goal_for_function! uart_tx_idle.
  Proof.
    (* TODO the proof is almost identical to one for uart_tx_idle_correct, but
       it is hard to generalize the proof becausae it calls the function twice *)
    repeat straightline.
    pose proof status_read_always_ok s as Hstat.
    destruct Hstat as (x & s' & Hstat).
    straightline_call; ssplit.
    { instantiate (1 := STATUS). apply word.ring_morph_add. }
    { cbv [state_machine.read_step uart_state_machine] in *. eauto. }
    { eauto. }
    { repeat straightline.
      straightline_call; eauto.
      repeat straightline.
      (* keep "execution a x" for later eassumption *)
      lazymatch goal with
      | H0 : execution tr _, H1: execution ?a _ |-  context [?tr] => rename H0 into Hexec; rename H1 into Hexec'
      end.
      pose proof Hexec' as HH.
      simpl in Hexec'.
      destruct Hexec' as (x' & Hexec').
      destruct Hexec'.
      replace s with x' in *.
      2:{ eapply execution_unique; eauto. }
      lazymatch goal with
      | H: step _ _ _ _ _ |- _ => unfold step in H; simpl in H
      end.
      logical_simplify.
      infer_reg_using_addr.
      do 3 eexists; ssplit; eauto.
      lazymatch goal with
      | H: [_] = [_] |- _ => inversion H; subst
      end.
      unfold UART_STATUS_TXIDLE_BIT in *.
      apply is_flag_set_and_select_bits; lia.
    }
  Qed.

  Ltac execution_trace Hexec Hexec' Hstep :=
    lazymatch Hexec with
    | execution ?t0 ?s0 =>
        lazymatch Hexec' with
        | execution ?t1 ?s1 =>
            lazymatch Hstep with
            | read_step s0 _ _ s1 => cbv [execution] in Hexec
            end
        end
    end.


  Global Instance spec_of_uart_putchar : spec_of "b2_uart_putchar" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) (s : state) byte,
      R m ->
      (* uart must be in IDLE state before putchar *)
      execution tr IDLE ->
      call function_env uart_putchar tr m [byte]
        (fun tr' m' rets =>
          exists (s' : state),
            (* uart must be in IDLE state after putchar *)
            execution tr' IDLE
            /\ R m'
            /\ rets = []).
  Lemma uart_putchar_correct :
    program_logic_goal_for_function! uart_putchar.
  Proof.
    repeat straightline.

    (* 1st while loop; we know that the loop will iterate once b/c s = IDLE *)
    eapply unroll_while with (iterations:=1%nat). cbn [repeat_logic_step].
    eexists.
    split; repeat straightline.
    subst cond.
    push_unsigned.
    rewrite word.eqb_eq.
    2:{ reflexivity. }
    split; [ lia | ].

    repeat straightline.
    (* calling uart_tx_full *)
    straightline_call; eauto; logical_simplify.
    repeat straightline.

    lazymatch goal with
    | H: read_step _ _ _ _ |- _ =>
        cbv [read_step] in H; logical_simplify
    end.

    lazymatch goal with
    | H: status_matches_state _ _ = true |- _ =>
        cbv [status_matches_state] in H; subst
    end.

    separate_flags.

    lazymatch goal with
        | H0 : _ = negb (is_flag_set _ UART_STATUS_TXFULL_BIT),
          H1 : negb (is_flag_set _ UART_STATUS_TXFULL_BIT) = true  |- _ =>
              rewrite H1 in H0; apply word.eqb_true in H0; subst
        end.

    split.
    {
      subst cond.
      push_unsigned.

      rewrite word.unsigned_eqb.
      rewrite word.unsigned_of_Z_1.
      rewrite word.unsigned_of_Z_0.
      reflexivity.
    }

    repeat straightline.

    (* call bitfield_field32_write *)
    straightline_call; eauto; repeat straightline.
    (* call abs_mmio_write32 *)
    straightline_call.
    {
      instantiate (1 := WDATA).
      rewrite <- word.ring_morph_add.
      cbv [state_machine.reg_addr uart_state_machine].
      unfold reg_addr. reflexivity. }
    {
      cbn [state_machine.write_step uart_state_machine].
      split; [reflexivity | ].
      instantiate (2 := IDLE).
      unfold write_step; reflexivity. }
    { eauto. }

    repeat straightline.

    lazymatch goal with
    | H0 : execution tr _, H1: execution ?a _ |-  context [?tr] => rename H0 into Hexec; rename H1 into Hexec'; subst a
    end.
    pose proof Hexec' as HH.
    simpl in Hexec'.
    destruct Hexec' as (x' & Hexec').
    destruct Hexec'.
    replace x' with IDLE in *.
    2:{ eapply execution_unique; eauto. }
    lazymatch goal with
    | H: step _ _ _ _ _ |- _ => unfold step in H; simpl in H
    end.
    logical_simplify.
    infer_reg_using_addr.

    lazymatch goal with
    | H: write_step _ _ _ ?x |- _ =>
        cbv [write_step] in H; subst x
    end.

    (* 2nd while loop *)
    (* loop until tx becomes IDLE again *)
    apply atleastonce_localsmap
      with (v0:=ncycles_processing)
           (lt:=lt)
           (invariant:=
             fun i tr m l =>
               execution tr (BUSY i) /\ R m).
    { apply lt_wf. }
    { (* Henter: case in which the loop breaks immediately (cannot happen) *)
      repeat straightline.
      exfalso. (* proof by contradiction *)

      subst cond.
      subst br.
      lazymatch goal with
      | H: word.unsigned _ = 0 |- _ =>
          rewrite word.unsigned_if in H;
          rewrite word.eqb_eq in H;
          rewrite word.unsigned_of_Z_1 in H;
          congruence
      end. }
    { (* Hpre: prof that invariant holds at loop start *)
      ssplit; eauto. }
    { (* Hbody *)
      repeat lazymatch goal with
             | H: execution ?a ?b |- _ => try clear dependent b; try clear dependent a; clear H
             end.
      repeat straightline.
      straightline_call; eauto.
      repeat straightline.

      cbv [read_step] in *.
      eexists; repeat straightline.
      {
        eexists.
        lazymatch goal with
        | |- map.get ?l _ = _ /\ _=> subst l
        end.
        rewrite map.get_put_same.
        ssplit; eauto.
        repeat straightline. }
      { (* continuation case -- invariant holds *)
        match goal with H : _ |- _ => apply word.if_nonzero, word.eqb_true in H end.
        subst.
        (* break into two possible s' : IDLE and BUSY *)
        lazymatch goal with H : _ \/ _ |- _ => destruct H end;
        logical_simplify; subst.
        { (* s' = IDLE (cannot happen, should have exitted) *)
          exfalso.
          lazymatch goal with
          | H: status_matches_state _ _ = true |- _ =>
              cbv [status_matches_state] in H; simpl in H
          end.
          separate_flags.

          lazymatch goal with
          | H: word.eqb _ _ = _,
          Hflag: is_flag_set _ UART_STATUS_TXIDLE_BIT = true |- _ =>
              rewrite word.eqb_eq in H; [ | reflexivity ]
                  ; rewrite <- Bool.negb_false_iff in Hflag
          end.

          lazymatch goal with
          | H0: negb (is_flag_set _ UART_STATUS_TXIDLE_BIT) = _,
            H1: true = negb (is_flag_set _ UART_STATUS_TXIDLE_BIT) |- _ =>
                rewrite <- H1 in H0
          end.
          congruence.
        }
        { (* s' = BUSY v' *)
          eexists.
          repeat straightline; ssplit; eauto.
        }
      }
      { (* break case -- postcondition holds *)
        (* break into two possible s' cases : IDLE and BUSY *)
        lazymatch goal with H : _ \/ _ |- _ => destruct H end;
        logical_simplify; subst.
        { (* s' = IDLE *)
          eexists; ssplit; eauto. }
        { (* s' = BUSY v' (cannot happen, should have continued) *)
          exfalso.
          cbv [status_matches_state] in *.

          separate_flags.

          autorewrite with push_unsigned in *.

          lazymatch goal with
          | H0: negb (is_flag_set _ UART_STATUS_TXIDLE_BIT) = _,
            H1: word.eqb _ _ = negb (is_flag_set _ UART_STATUS_TXIDLE_BIT) |- _ =>
                  rewrite <- H1 in H0;
                  apply word.eqb_true in H0; subst
          end.

          lazymatch goal with
          | H: (if _ then _ else _) = 0 |- _ => rewrite word.eqb_eq in H; [ | reflexivity ]
          end.
          congruence.
        }
      }
    }
  Qed.

End Proofs.
