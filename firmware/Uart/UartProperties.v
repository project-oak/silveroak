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
Require Import Bedrock2Experiments.LibBase.AbsMMIOReadProperties.
Require Import Bedrock2Experiments.LibBase.AbsMMIOWriteProperties.
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

  (* Plug in the right state machine parameters; typeclass inference struggles here *)
  Local Notation execution := (execution (M:=uart_state_machine)).

  (***** General-purpose lemmas/tactics and setup *****)

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Ltac solve_status_valid :=
    eexists; ssplit; try reflexivity;
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

  Lemma status_read_always_ok s :
    exists val s', read_step s STATUS val s'.
  Proof.
    destruct s; unfold read_step; cbn [read_step status_matches_state].
    { exists (word.or (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXEMPTY_BIT))
                      (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXIDLE_BIT))).
      solve_status_valid.
    }
    { destruct (Nat.eqb txlvl 0)%bool eqn:H.
      { apply Nat.eqb_eq in H. subst.
        exists (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXEMPTY_BIT)).
        solve_status_valid. }
      { destruct txlvl; [discriminate | ].
        destruct (Nat.ltb (S txlvl) 32)%bool eqn:Hl.
        { exists (word.of_Z 0).
          solve_status_valid. }
        { exists (word.slu (word.of_Z 1) (word.of_Z UART_STATUS_TXFULL_BIT)).
          solve_status_valid. }
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
        end.
    all:reflexivity.
  Qed.

  Lemma reg_is_status :
    forall r,
    reg_addr r = word.of_Z (TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET) ->
    r = STATUS.
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
    end.

  (***** Proofs for specific functions *****)

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
End Proofs.
