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
Require Import bedrock2.TailRecursion.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.letexists.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.WhileProperties.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.Aes.AesSemantics.
Require Import Bedrock2Experiments.Aes.Aes.
Require Import Bedrock2Experiments.Aes.Constants.
Import Syntax.Coercions List.ListNotations.
Local Open Scope Z_scope.

Section Proofs.
  Context {p : AesSemantics.parameters} {p_ok : parameters.ok p}
          {consts : aes_constants Z} {timing : timing}.
  Context {consts_ok : aes_constants_ok constant_words}.
  Existing Instance constant_words.
  Existing Instance state_machine_parameters.

  (***** General-purpose lemmas/tactics and setup *****)

  Add Ring wring : (Properties.word.ring_theory (word := parameters.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := parameters.word)),
         constants [Properties.word_cst]).

  Existing Instance constant_names | 10.

  (* This tactic simplifies implicit types so that they all agree; otherwise
     tactic has trouble connecting, for instance, a word of type parameters.word
     and a word of type Semantics.word, even though they are the same *)
  Local Ltac simplify_implicits :=
    change Semantics.word with parameters.word in *;
    change Semantics.mem with parameters.mem in *;
    change Semantics.width with 32 in *;
    change Semantics.word_ok with parameters.word_ok in *;
    change Semantics.mem_ok with parameters.mem_ok in *.

  Hint Extern 4 (step _ ?s _ _ _) =>
  eapply (ReadStep (p:=state_machine_parameters) s) : step.
  Hint Extern 4 (step _ ?s _ _ _) =>
  eapply (WriteStep (p:=state_machine_parameters) s) : step.

  Lemma word_add_0_r (w : parameters.word) : word.add w (word.of_Z 0) = w.
  Proof. ring. Qed.

  Lemma reg_addr_unique r1 r2 : reg_addr r1 = reg_addr r2 -> r1 = r2.
  Proof.
    pose proof addrs_unique as Huniq.
    cbv [aes_reg_addrs list_reg_addrs] in *.
    rewrite nregs_key_eq, nregs_iv_eq, nregs_data_eq in Huniq.
    repeat lazymatch type of Huniq with
           | context [Z.to_nat ?n] =>
             let x := constr:(Z.to_nat n) in
             let y := (eval vm_compute in x) in
             change x with y in Huniq
           | _ => progress cbn [seq map app] in Huniq
           end.
    simplify_unique_words_in Huniq.
    rewrite !word_add_0_r in *.
    cbv [reg_addr]; cbn; intro Heqaddr.
    destruct r1.
    (* clear all hypothesis that don't have to do with r1 (makes proof
       faster) *)
    all:lazymatch type of Heqaddr with
        | ?r = _ =>
          repeat match goal with
                 | H : ?x <> ?y |- _ =>
                   lazymatch x with
                   | context [r] => fail
                   | _ =>
                     lazymatch y with
                     | context [r] => fail
                     | _ => clear H
                     end
                   end
                 end
        end.
    all:destruct r2; try first [ exact eq_refl | congruence ].
  Qed.

  (* tactic to feed to [interaction] which will solve the side conditions of
     interact_mmio *)
  Local Ltac solve_dexprs :=
    repeat straightline_with_map_lookup;
    simplify_implicits; repeat straightline_with_map_lookup.

  (* run [interaction] and then assert the register's identity *)
  Local Ltac interaction_with_reg R :=
    (* this simplification step ensures that the parameters.reg_addr hypothesis
       we see is a new one *)
    cbn [parameters.reg_addr parameters.write_step parameters.read_step
                             state_machine_parameters] in *;
    interaction solve_dexprs;
    simplify_implicits;
    (* assert that the register address matches R *)
    lazymatch goal with
    | H : parameters.reg_addr ?r = ?addr |- _ =>
      replace addr with (reg_addr R) in H
        by (cbn [reg_addr]; subst_lets; ring);
      apply reg_addr_unique in H; try subst r
    end;
    (* simplify again *)
    cbn [parameters.reg_addr parameters.write_step parameters.read_step
                             state_machine_parameters] in *.

  Lemma execution_unique (t : trace) s1 s2 :
    execution t s1 ->
    execution t s2 ->
    s1 = s2.
  Proof.
    pose proof status_flags_unique_and_nonzero as Hflags.
    cbv [map] in Hflags.
    simplify_unique_words_in Hflags.
    revert s1 s2.
    induction t; cbn [execution]; [ congruence | ].
    intros; destruct_products.
    match goal with
    | H1 : execution t ?s1, H2 : execution t ?s2 |- _ =>
      specialize (IHt _ _ H1 H2); subst
    end.
    repeat invert_step;
      cbn [parameters.read_step parameters.write_step
                                state_machine_parameters] in *;
      cbv [read_step write_step] in *.
    all: repeat lazymatch goal with
                | H : False |- _ => contradiction H
                | H : _ /\ _ |- _ => destruct H
                | H : _ = reg_addr _ |- _ => apply reg_addr_unique in H; subst
                | |- ?x = ?x => reflexivity
                | _ => first [ progress subst
                            | destruct_one_match_hyp ]
                end.
  Qed.

  Local Ltac infer_states_equal :=
    repeat lazymatch goal with
           | H1 : execution ?t _, H2 : execution ?t _ |- _ =>
             pose proof execution_unique _ _ _ H1 H2; subst;
             clear H2; one_goal_or_solved ltac:(try congruence)
           end.

  Local Ltac infer_state_data_equal :=
    repeat lazymatch goal with
           | H : IDLE _ = IDLE _ |- _ => inversion H; clear H; subst
           | H : BUSY _ _ _ = BUSY _ _ _ |- _ => inversion H; clear H; subst
           | H : DONE _ = DONE _ |- _ => inversion H; clear H; subst
           end.

  Local Ltac invert_write_step_nobranch :=
    lazymatch goal with
    | H : write_step _ _ _ _ |- _ =>
      cbv [write_step] in H; cbn [reg_category] in H
    end;
    repeat lazymatch goal with
           | H : False |- _ => contradiction H
           | _ => destruct_one_match_hyp
           end; [ ].

  Local Ltac infer :=
    repeat first [ progress infer_states_equal
                 | progress infer_state_data_equal
                 | progress invert_write_step_nobranch
                 | progress invert_step ].

  (* Remove [execution] hypotheses that are superceded by later ones; improves
     proof performance *)
  (* Warning: be careful not to remove useful information with this tactic! *)
  Local Ltac clear_old_executions :=
    (* first call [infer] to help guard against losing information *)
    infer;
    repeat lazymatch goal with
           | H1 : execution ?t _, H2 : execution (_ :: ?t) _ |- _ =>
             clear H1
           end.

  Local Notation aes_op_t := (enum_member aes_op) (only parsing).
  Local Notation aes_mode_t := (enum_member aes_mode) (only parsing).
  Local Notation aes_key_len_t := (enum_member aes_key_len) (only parsing).

  Definition ctrl_operation (ctrl : parameters.word) : bool :=
    is_flag_set ctrl AES_CTRL_OPERATION.
  Definition ctrl_mode (ctrl : parameters.word) : parameters.word :=
    select_bits ctrl AES_CTRL_MODE_OFFSET AES_CTRL_MODE_MASK.
  Definition ctrl_key_len (ctrl : parameters.word) : parameters.word :=
    select_bits ctrl AES_CTRL_KEY_LEN_OFFSET AES_CTRL_KEY_LEN_MASK.
  Definition ctrl_manual_operation (ctrl : parameters.word) : bool :=
    is_flag_set ctrl AES_CTRL_MANUAL_OPERATION.

  (* prevent [inversion] from exposing word.of_Z in constants *)
  Local Opaque constant_words.

  (***** Proofs for specific functions *****)

  Instance spec_of_aes_init : spec_of aes_init :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop)
        aes_cfg_operation aes_cfg_mode aes_cfg_key_len
        aes_cfg_manual_operation,
        (* no special requirements of the memory *)
        R m ->
        (* circuit must start in UNINITIALIZED state *)
        execution tr UNINITIALIZED ->
        (* operation must be in the aes_op enum *)
        aes_op_t aes_cfg_operation ->
        (* mode must be in the aes_mode enum *)
        aes_mode_t aes_cfg_mode ->
        (* key length must be in the aes_key_len enum *)
        aes_key_len_t aes_cfg_key_len ->
        (* manual_operation is a boolean *)
        boolean aes_cfg_manual_operation ->
        let args := [aes_cfg_operation; aes_cfg_mode; aes_cfg_key_len;
                    aes_cfg_manual_operation] in
        call function_env aes_init tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                (* the circuit is in IDLE state with the correct control
                   register value and no other known register values *)
                (exists ctrl,
                    execution tr' (IDLE (map.put (map:=parameters.regs)
                                                 map.empty AES_CTRL ctrl))
                    /\ ctrl_operation ctrl = word.eqb aes_cfg_operation (word.of_Z 0)
                    /\ ctrl_mode ctrl = aes_cfg_mode
                    /\ ctrl_key_len ctrl = aes_cfg_key_len
                    /\ ctrl_manual_operation ctrl
                      = word.eqb aes_cfg_manual_operation (word.of_Z 0))
                (* ...and the same properties as before hold on the memory *)
                /\ R m'
                (* ...and there is no output *)
                /\ rets = []).


  Lemma aes_init_correct :
    program_logic_goal_for_function! aes_init.
  Proof.
    (* initial processing *)
    repeat straightline.

    (* write CTRL *)
    interaction_with_reg CTRL.
    repeat straightline.

    (* done; prove postcondition *)
    ssplit; auto; [ ].

    (* pose all the control-register formatting proofs *)
    pose proof operation_eq.
    pose proof mode_mask_eq.
    pose proof mode_offset_ok.
    pose proof key_len_mask_eq.
    pose proof key_len_offset_ok.
    pose proof manual_operation_ok.
    cbv [op_size] in *.
    repeat lazymatch goal with
           | H : enum_member _ _ |- _ =>
             apply enum_member_size in H;
               pose proof has_size_pos _ _ H
           end.

    (* infer information from the last step *)
    cbn [parameters.write_step state_machine_parameters] in *.
    infer; subst.

    simplify_implicits.

    (* split cases *)
    eexists; ssplit.
    { (* prove that the execution trace is OK *)
      eassumption. }
    { (* prove that the "operation" flag is correct *)
      cbv [ctrl_operation].
      rewrite !is_flag_set_or_shiftl_low by lia.
      apply is_flag_set_shift; eauto using size1_boolean.
      lia. }
    { cbv [ctrl_mode].
      erewrite !select_bits_or_shiftl_low, select_bits_or_shiftl_high
        by (first [ eassumption | prove_has_size | lia]).
      eapply select_bits_id; [ prove_has_size | .. ]; lia. }
    { cbv [ctrl_key_len].
      erewrite !select_bits_or_shiftl_low, select_bits_or_shiftl_high
        by (first [ eassumption | prove_has_size | lia]).
      eapply select_bits_id; [ prove_has_size | .. ]; lia. }
    { cbv [ctrl_manual_operation].
      apply is_flag_set_or_shiftl_high;
        (eassumption || prove_has_size || lia). }
  Qed.

  Instance spec_of_aes_key_put : spec_of aes_key_put :=
    fun function_env =>
      forall (tr : trace) (m : mem) R
        (rs : known_register_state)
        (key_len key_arr_ptr : Semantics.word) (key_arr : list Semantics.word),
        (* key_len is a member of the aes_key_len enum *)
        aes_key_len_t key_len ->
        (* key array is in memory *)
        (array scalar32 (word.of_Z 4) key_arr_ptr key_arr * R)%sep m ->
        (* key array length matches the key_len argument *)
         length key_arr = (if word.eqb key_len kAes128
                           then 4%nat else if word.eqb key_len kAes192
                                       then 6%nat else 8%nat) ->
        (* circuit must be in IDLE state *)
        execution tr (IDLE rs) ->
        let args := [key_arr_ptr; key_len] in
        call function_env aes_key_put tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                (* the circuit is in IDLE state with the key registers updated *)
                (exists rs',
                    map.putmany_of_list_zip
                      [reg_addr KEY0; reg_addr KEY1; reg_addr KEY2; reg_addr KEY3;
                      reg_addr KEY4; reg_addr KEY5; reg_addr KEY6; reg_addr KEY7]
                      (key_arr ++ repeat (word.of_Z 0) (8 - length key_arr)) rs
                    = Some rs'
                    /\ execution tr' (IDLE rs'))
                (* ...and the same properties as before hold on the memory *)
                /\ (array scalar32 (word.of_Z 4) key_arr_ptr key_arr * R)%sep m'
                (* ...and there is no output *)
                /\ rets = []).

  Local Ltac dexpr_hammer :=
    subst_lets; simplify_implicits;
    repeat first [ progress push_unsigned
                 | rewrite word.unsigned_of_Z in *
                 | rewrite word.wrap_small in * by lia
                 | destruct_one_match
                 | lia ].

  Lemma aes_key_put_correct :
    program_logic_goal_for_function! aes_key_put.
  Proof.
    (* initial processing *)
    repeat straightline.
    simplify_implicits.

    (* assert that key length enum members are unique *)
    pose proof enum_unique aes_key_len as key_len_unique.
    simplify_unique_words_in key_len_unique.

    (* key_len must be one of the members of the aes_key_len enum *)
    lazymatch goal with
    | H : enum_member aes_key_len ?len |- _ =>
      cbn [enum_member aes_key_len In] in H
    end.

    (* this assertion helps prove that i does not get truncated *)
    assert (8 < 2 ^ Semantics.width) by (cbn; lia).
    pose proof nregs_key_eq.

    (* destruct branches *)
    split_if; [ | intros; split_if ]; intros;
      repeat lazymatch goal with
             | H : word.unsigned _ <> 0 |- _ =>
               apply word.if_nonzero, word.eqb_true in H
             | H : word.unsigned _ = 0 |- _ =>
               apply word.if_zero, word.eqb_false in H
             end; subst.

    (* use key_len information to destruct cases in preconditions and get
       individual keys *)
    all:(repeat (destruct_one_match_hyp_of_type bool; try congruence);
         repeat lazymatch goal with
                | H : _ \/ _ |- _ => destruct H; try congruence
                end; [ ]).
    all:destruct_lists_by_length.

    (* simplify array predicate *)
    all:cbn [array] in *.
    all:repeat match goal with
               | H : context [scalar32 ?addr] |- _ =>
                 progress ring_simplify addr in H
               end.

    { (* key_len = kAes256 case *)
      repeat straightline.

      (* unroll first while loop *)
      eapply unroll_while with (iterations:=8%nat). cbn [repeat_logic_step].
      repeat straightline.

      (* process each iteration of the while loop *)

      (* i = 0 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY0.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 1 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY1.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 2 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY2.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 3 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY3.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 4 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY4.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 5 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY5.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 6 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY6.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 7 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY7.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 8; loop done *)
      ssplit; repeat straightline; [ dexpr_hammer | ].

      (* second while loop is a no-op *)
      eapply unroll_while with (iterations:=0%nat). cbn [repeat_logic_step].
      ssplit; repeat straightline; [ dexpr_hammer | ].

      (* done; prove postcondition *)
      ssplit; eauto; [ | ].
      { (* trace postcondition *)
        eexists; split; [ reflexivity | ].
        eassumption. }
      { (* memory postcondition *)
        cbn [array].
        repeat match goal with
               | |- context [scalar32 ?addr] =>
                 progress ring_simplify addr
               end.
        ecancel_assumption. } }

    { (* key_len = kAes192 case *)
      repeat straightline.

      (* unroll first while loop *)
      eapply unroll_while with (iterations:=6%nat). cbn [repeat_logic_step].
      repeat straightline.

      (* process each iteration of the while loop *)

      (* i = 0 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY0.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 1 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY1.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 2 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY2.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 3 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY3.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 4 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY4.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 5 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY5.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 6; loop done *)
      ssplit; repeat straightline; [ dexpr_hammer | ].

      (* second while loop has 8 - 6 = 2 iterations *)
      eapply unroll_while with (iterations:=2%nat). cbn [repeat_logic_step].
      repeat straightline.

      (* i = 6 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY6.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 7 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY7.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 8; loop done *)
      ssplit; repeat straightline; [ dexpr_hammer | ].

      (* done; prove postcondition *)
      ssplit; eauto; [ | ].
      { (* trace postcondition *)
        eexists; split; [ reflexivity | ].
        eassumption. }
      { (* memory postcondition *)
        cbn [array].
        repeat match goal with
               | |- context [scalar32 ?addr] =>
                 progress ring_simplify addr
               end.
        ecancel_assumption. } }

    { (* key_len = kAes128 case *)
      repeat straightline.

      (* unroll first while loop *)
      eapply unroll_while with (iterations:=4%nat). cbn [repeat_logic_step].
      repeat straightline.

      (* process each iteration of the while loop *)

      (* i = 0 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY0.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 1 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY1.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 2 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY2.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 3 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY3.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 4; loop done *)
      ssplit; repeat straightline; [ dexpr_hammer | ].

      (* second while loop has 8 - 4 = 4 iterations *)
      eapply unroll_while with (iterations:=4%nat). cbn [repeat_logic_step].
      repeat straightline.

      (* i = 4 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY4.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 5 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY5.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 6 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY6.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 7 *)
      split; repeat straightline; [ dexpr_hammer | ].
      interaction_with_reg KEY7.
      infer; subst; clear_old_executions.
      repeat straightline.

      (* i = 8; loop done *)
      ssplit; repeat straightline; [ dexpr_hammer | ].

      (* done; prove postcondition *)
      ssplit; eauto; [ | ].
      { (* trace postcondition *)
        eexists; split; [ reflexivity | ].
        eassumption. }
      { (* memory postcondition *)
        cbn [array].
        repeat match goal with
               | |- context [scalar32 ?addr] =>
                 progress ring_simplify addr
               end.
        ecancel_assumption. } }
  Qed.

  Instance spec_of_aes_iv_put : spec_of aes_iv_put :=
    fun function_env =>
      forall (tr : trace) (m : mem) R
        (rs : known_register_state)
        (iv_ptr iv0 iv1 iv2 iv3 : Semantics.word),
        (* iv array is in memory *)
        (array scalar32 (word.of_Z 4) iv_ptr [iv0;iv1;iv2;iv3] * R)%sep m ->
        (* circuit must be in IDLE state *)
        execution tr (IDLE rs) ->
        let args := [iv_ptr] in
        call function_env aes_iv_put tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                (* the circuit is in IDLE state with the iv registers updated *)
                execution tr'
                          (IDLE (map.putmany_of_list
                                   [(reg_addr IV0, iv0)
                                    ; (reg_addr IV1, iv1)
                                    ; (reg_addr IV2, iv2)
                                    ; (reg_addr IV3, iv3)] rs))
                (* ...and the same properties as before hold on the memory *)
                /\ (array scalar32 (word.of_Z 4) iv_ptr [iv0;iv1;iv2;iv3] * R)%sep m'
                (* ...and there is no output *)
                /\ rets = []).

  Lemma aes_iv_put_correct :
    program_logic_goal_for_function! aes_iv_put.
  Proof.
    (* initial processing *)
    repeat straightline.
    simplify_implicits.

    (* simplify array predicate *)
    cbn [array] in *.
    repeat match goal with
           | H : context [scalar32 ?addr] |- _ =>
             progress ring_simplify addr in H
           end.

    (* this assertion helps prove that i does not get truncated *)
    assert (4 < 2 ^ Semantics.width) by (cbn; lia).
    pose proof nregs_iv_eq.

    (* unroll while loop *)
    eapply unroll_while with (iterations:=4%nat). cbn [repeat_logic_step].
    repeat straightline.

    (* process each iteration of the while loop *)

    (* i = 0 *)
    split; repeat straightline; [ dexpr_hammer | ].
    interaction_with_reg IV0. infer; subst.
    repeat straightline.

    (* i = 1 *)
    split; repeat straightline; [ dexpr_hammer | ].
    interaction_with_reg IV1. infer; subst.
    repeat straightline.

    (* i = 2 *)
    split; repeat straightline; [ dexpr_hammer | ].
    interaction_with_reg IV2. infer; subst.
    repeat straightline.

    (* i = 3 *)
    split; repeat straightline; [ dexpr_hammer | ].
    interaction_with_reg IV3. infer; subst.
    repeat straightline.

    (* i = 4; loop done *)
    ssplit; repeat straightline; [ dexpr_hammer | ].

    (* done; prove postcondition *)
    cbn [array].
    repeat match goal with
           | |- context [scalar32 ?addr] =>
             progress ring_simplify addr
           end.
    ssplit; eauto.
  Qed.
End Proofs.
