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

  Local Ltac invert_step :=
    lazymatch goal with
    | H : step _ _ _ _ _ |- _ => inversion H; clear H; subst
    end.

  Lemma execution_step action args rets t s s':
    execution t s -> step action s args rets s' ->
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s'.
  Proof. intros; cbn [execution]; eauto. Qed.
  Lemma invert1_execution action args rets t s':
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s' ->
    exists s, execution t s /\ step action s args rets s'.
  Proof. intros; cbn [execution]; eauto. Qed.

  Lemma interact_mmio call action binds arges t m l
        (post : trace -> mem -> locals -> Prop) (args : list Semantics.word) :
    dexprs m l arges args ->
    (forall s' (rets : list Semantics.word),
        execution ((map.empty, action, args, (map.empty, rets)) :: t) s' ->
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
    (* get trace *)
    let t := lazymatch goal with
             | |- cmd _ (cmd.interact _ _ _) ?t _ _ _ => t end in
    eapply interact_mmio;
    [ solve [repeat straightline_with_map_lookup;
             simplify_implicits; repeat straightline_with_map_lookup] | ];
    simplify_implicits; intros;
    lazymatch goal with
    | H : execution (_ :: t) _ |- _ =>
      pose proof H; apply invert1_execution in H; destruct H as [? [? ?]]
    end; invert_step; repeat straightline.

  Fixpoint repeat_logic_step
           (logic : Semantics.trace -> Semantics.mem -> Semantics.locals ->
                    (Semantics.trace -> Semantics.mem -> Semantics.locals -> Prop) -> Prop)
           (n : nat) post : Semantics.trace -> Semantics.mem -> locals -> Prop :=
    match n with
    | O => post
    | S n => fun t m l => logic t m l (repeat_logic_step logic n post)
    end.

  Lemma unroll_while functions conde body t m l
        (iterations : nat)
        (post : trace -> mem -> locals -> Prop) (cond : Semantics.word) :
    repeat_logic_step
      (fun t m l post =>
         exists cond,
           dexpr m l conde cond
           /\ word.unsigned cond <> 0
           /\ cmd (call functions) body t m l post)
      iterations (fun t m l =>
                    dexpr m l conde cond
                    /\ word.unsigned cond = 0
                    /\ post t m l) t m l ->
    cmd (call functions) (cmd.while conde body) t m l post.
  Proof.
    lazymatch goal with
      |- repeat_logic_step ?logic _ ?post _ _ _ -> _ =>
      set (step:=logic);
        set (P:=post)
    end.
    intros. exists nat, lt, (fun i => repeat_logic_step step i P).
    ssplit.
    { exact lt_wf. }
    { eauto. }
    { intro i. destruct i; cbn [repeat_logic_step].
      { (* i=0 case (contradiction) *)
        subst P. repeat straightline.
        eexists; ssplit; eauto; congruence. }
      { (* i <> 0 case *)
        subst step. repeat straightline.
        eexists; ssplit; eauto; try congruence; [ ].
        repeat straightline.
        eapply Proper_cmd; [ apply Proper_call | | eassumption ].
        repeat intro. exists i. ssplit; eauto. } }
  Qed.

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

  (* run [interaction] and then assert the register's identity *)
  Local Ltac interaction_with_reg R :=
    (* this simplification step ensures that the parameters.reg_addr hypothesis
       we see is a new one *)
    cbn [parameters.reg_addr parameters.write_step parameters.read_step
                             state_machine_parameters] in *;
    interaction;
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

  Lemma ControlReg_is_CTRL r : reg_category r = ControlReg -> r = CTRL.
  Proof. destruct r; cbn [reg_category]; congruence. Qed.

  Local Ltac infer_registers_equal :=
    repeat lazymatch goal with
           | H : reg_category _ = ControlReg |- _ =>
             apply ControlReg_is_CTRL in H; subst
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
    repeat first [ progress infer_registers_equal
                 | progress infer_states_equal
                 | progress infer_state_data_equal
                 | progress invert_write_step_nobranch
                 | progress invert_step ].

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
    interaction.

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
    infer.

    simplify_implicits.

    (* split cases *)
    eexists; ssplit.
    { (* prove that the execution trace is OK *)
      eapply execution_step; eauto; [ ].
      econstructor; eauto; reflexivity. }
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
                          (IDLE (map.put
                                   (map.put
                                      (map.put
                                         (map.put rs (reg_addr IV0) iv0)
                                         (reg_addr IV1) iv1)
                                      (reg_addr IV2) iv2)
                                   (reg_addr IV3) iv3))
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

    (* unroll while loop *)
    eapply unroll_while with (iterations:=4%nat). cbn [repeat_logic_step].
    repeat straightline.

    (* process each iteration of the while loop *)

    (* i = 0 *)
    split; repeat straightline.
    { subst_lets. simplify_implicits. push_unsigned.
      rewrite nregs_iv_eq. destruct_one_match; lia. }
    interaction_with_reg IV0. infer; subst.

    (* i = 1 *)
    split; repeat straightline.
    { subst_lets. simplify_implicits. push_unsigned.
      rewrite nregs_iv_eq. destruct_one_match; lia. }
    interaction_with_reg IV1. infer; subst.

    (* i = 2 *)
    split; repeat straightline.
    { subst_lets. simplify_implicits. push_unsigned.
      rewrite nregs_iv_eq. destruct_one_match; lia. }
    interaction_with_reg IV2. infer; subst.

    (* i = 3 *)
    split; repeat straightline.
    { subst_lets. simplify_implicits. push_unsigned.
      rewrite nregs_iv_eq. destruct_one_match; lia. }
    interaction_with_reg IV3. infer; subst.

    (* i = 4; loop done *)
    ssplit; repeat straightline; [ | ].
    { subst_lets. simplify_implicits. push_unsigned.
      rewrite nregs_iv_eq. destruct_one_match; lia. }

    (* done; prove postcondition *)
    cbn [array].
    repeat match goal with
           | |- context [scalar32 ?addr] =>
             progress ring_simplify addr
           end.
    ssplit; eauto.
  Qed.
End Proofs.
