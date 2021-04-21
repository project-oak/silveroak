Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.TailRecursion.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.letexists.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.Tactics.
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

  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).

  Existing Instance constant_names | 10.

  Lemma interact_mmio call action binds arges t m l
        (post : trace -> mem -> locals -> Prop) (args : list Semantics.word) :
    dexprs m l arges args ->
    (forall s s' (rets : list Semantics.word),
        execution t s ->
        step action s args rets s' ->
        (exists l0 : locals,
            map.putmany_of_list_zip binds rets l = Some l0 /\
            post ((map.empty, action, args, (map.empty, rets)) :: t) m l0)) ->
    cmd call (cmd.interact binds action arges) t m l post.
  Proof.
    intros. eapply interact_nomem; [ eassumption | ].
    cbn [Semantics.ext_spec semantics_parameters].
    cbv [ext_spec]. split; [reflexivity | ].
    intros. split; [ reflexivity | ].
    cbn [execution] in *; destruct_products.
    eauto.
  Qed.

  Local Ltac interaction :=
    eapply interact_mmio; [ solve [repeat straightline_with_map_lookup] | ];
    repeat straightline;
    lazymatch goal with
    | H : step _ _ _ _ _ |- _ => inversion H; clear H; subst
    end.

  Hint Extern 4 (step _ ?s _ _ _) =>
  eapply (ReadStep (p:=state_machine_parameters) s) : step.
  Hint Extern 4 (step _ ?s _ _ _) =>
  eapply (WriteStep (p:=state_machine_parameters) s) : step.
  Hint Constructors read_step : step.
  Hint Constructors write_step : step.

  Lemma reg_addr_unique r1 r2 : reg_addr r1 = reg_addr r2 -> r1 = r2.
  Proof.
    assert (forall w, word.add w (word.of_Z 0) = w) as word_add_0
        by (intros; ring).
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
    rewrite !word_add_0 in *. clear word_add_0.
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
    repeat (lazymatch goal with
            | x := _ |- _ => subst x
            | |- ?x = ?x => reflexivity
            | H : is_busy (BUSY _ _ _) = false |- _ =>
              cbv [is_busy] in H; exfalso; congruence
            | H : parameters.reg_addr _ = reg_addr _ |- _ =>
              apply reg_addr_unique in H; subst
            | H : step _ _ _ _ _ |- _ =>
              inversion H; clear H; subst
            | H : parameters.read_step _ _ _ _ |- _ =>
              inversion H; clear H; subst
            | H : parameters.write_step _ _ _ _ |- _ =>
              inversion H; clear H; subst
            | _ => first [ invert_bool
                        | progress cbn [status_matches_state
                                          is_input_reg
                                          is_output_reg] in *]
            end; try congruence).
  Qed.

  Local Ltac infer_states_equal :=
    repeat match goal with
           | H1 : execution ?t _, H2 : execution ?t _ |- _ =>
             pose proof execution_unique _ _ _ H1 H2; subst;
             clear H2; one_goal_or_solved ltac:(try congruence)
           end.

  Lemma execution_step action args rets t s s':
    execution t s -> step action s args rets s' ->
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s'.
  Proof. intros; cbn [execution]; eauto. Qed.

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
                                                 map.empty (AES_CTRL : Semantics.word) ctrl))
                    /\ ctrl_operation ctrl = word.eqb aes_cfg_operation (word.of_Z 0)
                    /\ ctrl_mode ctrl = aes_cfg_mode
                    /\ ctrl_key_len ctrl = aes_cfg_key_len
                    /\ ctrl_manual_operation ctrl
                      = word.eqb aes_cfg_manual_operation (word.of_Z 0))
                (* ...and the same properties as before hold on the memory *)
                /\ R m'
                (* ...and there is no output *)
                /\ rets = []).

  (* prevent [inversion] from exposing word.of_Z in constants *)
  Opaque constant_words.

  Lemma aes_init_correct :
    program_logic_goal_for_function! aes_init.
  Proof.
    (* initial processing *)
    repeat straightline.

    (* write CTRL *)
    interaction.
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
    infer_states_equal.
    cbn [parameters.write_step state_machine_parameters] in *.
    lazymatch goal with
    | H : write_step _ ?r ?v _ |- _ =>
      inversion H; subst
    end; [ ].

    (* make sure implicit types all agree *)
    change Semantics.word with parameters.word in *.
    change Semantics.width with 32 in *.
    change Semantics.word_ok with parameters.word_ok in *.

    (* split cases *)
    eexists; ssplit.
    { (* prove that the execution trace is OK *)
      eapply execution_step; eauto with step. }
    { (* prove that the "operation" flag is correct *)
      cbv [ctrl_operation]. clear H11.
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
End Proofs.
