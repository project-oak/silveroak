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
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.letexists.
Require Import coqutil.Z.Lia.
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
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Section Proofs.
  Context {p : AesSemantics.parameters} {p_ok : parameters.ok p}
          {consts : aes_constants Z} {timing : timing}.
  Context {consts_ok : aes_constants_ok constant_words}.
  Existing Instance constant_words.
  Existing Instance state_machine_parameters.

  (* this duplicate of locals_ok helps when Semantics.word has been changed to
     parameters.word *)
  Local Instance localsok : @map.ok string parameters.word Semantics.locals
    := Semantics.locals_ok.

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

  (* alternate form of reg_addr_unique *)
  Lemma reg_addr_neq r1 r2 : r1 <> r2 -> reg_addr r1 <> reg_addr r2.
  Proof.
    intros. intro Heq. apply reg_addr_unique in Heq. congruence.
  Qed.

  (* TODO: move to Util/List *)
  Lemma existsb_nexists {A} (f : A -> bool) l : existsb f l = false <-> (forall x, In x l -> f x = false).
  Proof.
    split.
    { induction l; intros; cbn [In existsb] in *; [ tauto | ].
      repeat lazymatch goal with
             | H : (_ || _)%bool = false |- _ => apply Bool.orb_false_iff in H; destruct H
             | H : _ \/ _ |- _ => destruct H
             | _ => subst; eauto; congruence
             end. }
    { induction l; intros; cbn [In existsb] in *; [ tauto | ].
      rewrite IHl by auto. rewrite Bool.orb_false_r. eauto. }
  Qed.

  (*
  Lemma addr_in_category_reg_addr r c :
    addr_in_category (reg_addr r) c = reg_category_eqb c (reg_category r).
  Proof.
    cbv [addr_in_category].
    case_eq (reg_category_eqb c (reg_category r)); intros.
    { apply existsb_exists; exists r.
      split; [ apply all_regs_complete | ].
      apply Bool.andb_true_iff; split; [ apply word.eqb_eq; reflexivity | ].
      congruence. }
    { apply existsb_nexists; intro r2. intros.
      apply Bool.andb_false_iff.
      destr (word.eqb (reg_addr r) (reg_addr r2)).
      { lazymatch goal with
          H : reg_addr _ = reg_addr _ |- _ => apply reg_addr_unique in H end.
        subst. tauto. }
      { left. apply word.eqb_ne; auto. } }
  Qed.

  Lemma nregs_populated_put rs r v cat :
    reg_lookup rs r = None ->
    nregs_populated (map.put rs (reg_addr r) v) cat =
    if reg_category_eqb cat (reg_category r)
    then S (nregs_populated rs cat)
    else nregs_populated rs cat.
  Proof.
    cbv [nregs_populated reg_lookup]. intros.
    rewrite map.fold_put; auto.
    { rewrite addr_in_category_reg_addr. reflexivity. }
    { intros. repeat destruct_one_match; reflexivity. }
  Qed.

  Lemma nregs_populated_remove rs r cat v :
    reg_lookup rs r = Some v ->
    nregs_populated (map.remove rs (reg_addr r)) cat =
    if reg_category_eqb cat (reg_category r)
    then (nregs_populated rs cat - 1)%nat
    else nregs_populated rs cat.
  Proof.
    cbv [nregs_populated reg_lookup]. intros.
    erewrite map.fold_remove with (m:=rs); eauto; [ | ].
    { rewrite addr_in_category_reg_addr.
      destruct_one_match; try reflexivity. lia. }
    { intros. repeat destruct_one_match; reflexivity. }
  Qed.

  Lemma regs_empty_impl rs c r :
    nregs_populated rs c = 0%nat ->
    reg_category_eqb c (reg_category r) = true ->
    reg_lookup rs r = None.
  Proof.
    intros. revert dependent rs.
    cbv [nregs_populated].
    apply (map.fold_spec (fun rs count => count = 0%nat -> reg_lookup rs r = None));
      intros; [ apply map.get_empty | ].
    cbv [reg_lookup] in *.
    destruct_one_match_hyp; try congruence; [ ].
    rewrite map.get_put_dec.
    destruct_one_match; subst; [ | tauto ].
    rewrite addr_in_category_reg_addr in *.
    congruence.
  Qed.

  Lemma regs_lookup_put rs r1 r2 v :
    r1 <> r2 -> reg_lookup rs r1 = None ->
    reg_lookup (map.put rs (reg_addr r2) v) r1 = None.
  Proof.
    cbv [reg_lookup]. intros.
    rewrite map.get_put_diff by (apply reg_addr_neq; congruence).
    assumption.
  Qed.

  Lemma unset_inp_regs_put rs r v :
    unset_inp_regs (map.put rs (reg_addr r) v) =
    if (reg_category_eqb DataInReg (reg_category r)
        || reg_category_eqb IVReg (reg_category r)
        || reg_category_eqb KeyReg (reg_category r))%bool
    then unset_inp_regs rs
    else map.put (unset_inp_regs rs) (reg_addr r) v.
  Proof.
    cbv [unset_inp_regs]. apply map.map_ext; intros.
    destruct_one_match.
    { rewrite !map.get_remove_dec.
      repeat (destruct_one_match; try reflexivity); [ ].
      apply map.get_put_diff.
      destruct r; cbn [reg_category reg_category_eqb orb] in *; congruence. }
    { repeat lazymatch goal with H : (_ || _)%bool = false |- _ =>
                                 apply Bool.orb_false_iff in H; destruct H end.
      repeat lazymatch goal with
               | |- context [map.get (map.put _ _ _) _] => rewrite map.get_put_dec
               | |- context [map.get (map.remove _ _) _] => rewrite map.get_remove_dec
               | H : reg_addr _ = reg_addr _ |- _ =>
                 apply reg_addr_unique in H; subst;
                   cbn [reg_category reg_category_eqb] in *; try congruence
               | _ => destruct_one_match; subst; try reflexivity
               end. }
  Qed.
   *)
  (* tactic to solve the side conditions of interact_read and interact_write *)
  Local Ltac solve_dexprs ::=
    repeat straightline_with_map_lookup;
    simplify_implicits; repeat straightline_with_map_lookup.

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
    cbv [step] in *. cbn [ parameters.read_step
                             parameters.write_step
                             state_machine_parameters] in *.
    repeat destruct_one_match_hyp; try congruence; [ | ].
    all:logical_simplify; subst.
    all: lazymatch goal with
         | H : parameters.reg_addr ?x = parameters.reg_addr ?y |- _ =>
           eapply (parameters.reg_addr_unique
                     (ok:=state_machine_parameters_ok) x y) in H
         end.
    all:cbv [write_step read_step] in *; subst.
    all:repeat destruct_one_match_hyp; try congruence.
    all:logical_simplify; subst.
    all:lazymatch goal with
        | H : False |- _ => contradiction H
        | _ => reflexivity
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

  Local Ltac infer :=
    repeat first [ progress infer_states_equal
                 | progress infer_state_data_equal ].

  Lemma status_read_always_ok s :
    exists val s', read_step s STATUS val s'.
  Proof.
    destruct s; cbn [read_step reg_category].
    all:do 2 eexists.
  Admitted. (* TODO *)

  (* solve common side conditions from interactions *)
  Local Ltac post_interaction :=
    lazymatch goal with
    | |- dexprs _ _ _ _ => solve_dexprs; reflexivity
    | |- reg_addr _ = _ => reflexivity
    | |- execution _ _ => eassumption
    | |- ?G => tryif is_lia G then lia else eauto
    end.

  Lemma interact_read_status s call bind addre t m l
        (post : trace -> mem -> locals -> Prop) addr :
    dexprs m l [addre] [addr] ->
    reg_addr STATUS = addr ->
    execution t s ->
    (forall s' val,
        read_step s STATUS val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, READ, [addr], (map.empty, [val])) :: t) s' ->
        post ((map.empty, READ, [addr], (map.empty, [val])) :: t)
             m (map.put l bind val)) ->
    cmd call (cmd.interact [bind] READ [addre]) t m l post.
  Proof.
    intros; eapply interact_read; intros; infer;
      cbv [parameters.read_step state_machine_parameters] in *;
      eauto.
    pose proof status_read_always_ok s. logical_simplify.
    do 3 eexists; eauto.
  Qed.

  Lemma interact_write_control s call addre vale t m l
        (post : trace -> mem -> locals -> Prop) addr val :
    dexprs m l [addre; vale] [addr; val] ->
    reg_addr CTRL = addr ->
    execution t s ->
    match s with
    | IDLE _ => True
    | UNINITIALIZED => True
    | _ => False
    end ->
    (forall s',
        write_step s CTRL val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t) s' ->
        post ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t)
             m l) ->
    cmd call (cmd.interact [] WRITE [addre;vale]) t m l post.
  Proof.
    intros; eapply interact_write; intros; infer;
      cbv [parameters.write_step state_machine_parameters] in *;
      eauto.
    cbv [write_step]. cbn [reg_category].
    exists s; destruct s; try contradiction;
      eexists; ssplit; (assumption || reflexivity).
  Qed.

  Definition key_from_index (i : nat) : Register :=
    nth i [KEY0;KEY1;KEY2;KEY3;KEY4;KEY5;KEY6;KEY7] CTRL.

  Lemma key_from_index_category i :
    (i < 8)%nat -> reg_category (key_from_index i) = KeyReg.
  Proof.
    intros. cbv [key_from_index].
    apply Forall_nth; [ |  length_hammer ].
    repeat constructor.
  Qed.

  Lemma interact_write_key i call addre vale t m l
        (post : trace -> mem -> locals -> Prop) rs addr val :
    dexprs m l [addre; vale] [addr; val] ->
    addr = word.add AES_KEY0 (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4)) ->
    (i < 8)%nat ->
    execution t (IDLE rs) ->
    (forall s',
        write_step (IDLE rs) (key_from_index i) val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t) s' ->
        post ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t)
             m l) ->
    cmd call (cmd.interact [] WRITE [addre;vale]) t m l post.
  Proof.
    intros; eapply interact_write; intros; infer;
      cbv [parameters.write_step state_machine_parameters] in *;
      eauto.
    { repeat (destruct i; try lia); subst; cbn; ring. }
    { cbv [write_step]. rewrite key_from_index_category by lia.
      exists (IDLE rs). eexists; ssplit; eauto. }
  Qed.

  Definition iv_from_index (i : nat) : Register :=
    nth i [IV0;IV1;IV2;IV3] CTRL.

  Lemma iv_from_index_category i :
    (i < 4)%nat -> reg_category (iv_from_index i) = IVReg.
  Proof.
    intros. cbv [iv_from_index].
    apply Forall_nth; [ | length_hammer ].
    repeat constructor.
  Qed.

  Lemma interact_write_iv i call addre vale t m l
        (post : trace -> mem -> locals -> Prop) rs addr val :
    dexprs m l [addre; vale] [addr; val] ->
    addr = word.add AES_IV0 (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4)) ->
    (i < 4)%nat ->
    execution t (IDLE rs) ->
    (forall s',
        write_step (IDLE rs) (iv_from_index i) val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t) s' ->
        post ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t)
             m l) ->
    cmd call (cmd.interact [] WRITE [addre;vale]) t m l post.
  Proof.
    intros; eapply interact_write; intros; infer;
      cbv [parameters.write_step state_machine_parameters] in *;
      eauto.
    { repeat (destruct i; try lia); subst; cbn; ring. }
    { cbv [write_step]. rewrite iv_from_index_category by lia.
      exists (IDLE rs). eexists; ssplit; eauto. }
  Qed.

  Local Ltac read_status :=
    eapply interact_read_status; [ try post_interaction .. | ].
  Local Ltac write_control :=
    eapply interact_write_control; [ try post_interaction .. | ].
  Local Ltac write_key :=
    eapply interact_write_key;
    [ try post_interaction ..
    | intros;
      try lazymatch goal with
          | H : write_step _ _ _ _ |- _ =>
            cbv [write_step] in H;
            rewrite key_from_index_category in H by lia; subst
          end ].
  Local Ltac write_iv_n n :=
    eapply interact_write_iv with (i:=n);
    [ try post_interaction ..
    | intros;
      try lazymatch goal with
          | H : write_step _ _ _ _ |- _ =>
            cbv [write_step] in H;
            rewrite iv_from_index_category in H by lia; subst
          end ].
  (*
  Local Ltac invert_read_step :=
    lazymatch goal with
    | H : read_step _ _ _ _ |- _ =>
      cbv [read_step] in H; cbn [reg_category] in H
    end;
    logical_simplify; simplify_implicits;
    repeat lazymatch goal with
           | H : False |- _ => contradiction H
           | Heq : nregs_populated _ ?c = _,
                   H : context [nregs_populated (map.remove ?m _) ?c] |- _ =>
             erewrite !nregs_populated_remove in H by eauto;
               simplify_implicits; rewrite Heq in H;
                 cbn [reg_category reg_category_eqb Nat.sub] in H
           | H : S _ = O |- _ => lia
           | H : O <> O |- _ => lia
           | _ => first [ destruct_one_match_hyp
                       | progress logical_simplify ]
           end.

  Local Ltac invert_write_step :=
    lazymatch goal with
    | H : write_step _ _ _ _ |- _ =>
      cbv [write_step] in H; cbn [reg_category] in H
    end;
    repeat lazymatch goal with
           | Hemp : nregs_populated _ ?c = 0%nat,
                    H : context [nregs_populated (map.put _ _ _) ?c] |- _ =>
             rewrite !nregs_populated_put in H
               by (repeat (apply regs_lookup_put; [ congruence | ]);
                   eauto using regs_empty_impl);
             rewrite Hemp in H;
             cbn [reg_category reg_category_eqb Nat.eqb] in H; subst
           | H : False |- _ => contradiction H
           | _ => first [ destruct_one_match_hyp
                       | progress logical_simplify ]
           end.
   *)

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

  Definition get_known_regs (s : state) : known_register_state :=
    match s with
    | UNINITIALIZED => map.empty
    | IDLE rs => rs
    | BUSY rs _ _ => rs
    | DONE rs => rs
    end.

  (* prevent [inversion] from exposing word.of_Z in constants *)
  Local Opaque constant_words.

  (***** Proofs for specific functions *****)

  Global Instance spec_of_aes_data_ready : spec_of aes_data_ready :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) (s : state),
        (* no special requirements of the memory *)
        R m ->
        (* no constraints on current state *)
        execution tr s ->
        let args := [] in
        call function_env aes_data_ready tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                exists (status out : Semantics.word) (s' : state),
                  (* trace has exactly one new read value *)
                  tr' = (map.empty, READ, [AES_STATUS],(map.empty,[status])) :: tr
                  (* ...and there is a new state matching the new trace *)
                  /\ execution tr' s'
                  (* ...and all the same properties as before hold on the memory *)
                  /\ R m'
                  (* ...and there is one output value *)
                  /\ rets = [out]
                  (* ...and the output value is zero if and only if the
                     input_ready flag is unset *)
                  /\ word.eqb out (word.of_Z 0)
                    = negb (is_flag_set status AES_STATUS_INPUT_READY)).

  Lemma aes_data_ready_correct :
    program_logic_goal_for_function! aes_data_ready.
  Proof.
    (* initial processing *)
    repeat straightline.

    read_status.
    repeat straightline.

    (* done; prove postcondition *)
    do 3 eexists. ssplit; eauto; [ ].
    subst_lets. cbv [is_flag_set].
    boolsimpl. reflexivity.
  Qed.

  Global Instance spec_of_aes_data_valid : spec_of aes_data_valid :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) (s : state),
        (* no special requirements of the memory *)
        R m ->
        (* no constraints on current state *)
        execution tr s ->
        let args := [] in
        call function_env aes_data_valid tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                exists (status out : Semantics.word) (s' : state),
                  (* trace has exactly one new read value *)
                  tr' = (map.empty, READ, [AES_STATUS],(map.empty,[status])) :: tr
                  (* ...and there is a new state matching the new trace *)
                  /\ execution tr' s'
                  (* ...and all the same properties as before hold on the memory *)
                  /\ R m'
                  (* ...and there is one output value *)
                  /\ rets = [out]
                  (* ...and the output value is zero if and only if the
                     output_valid flag is unset *)
                  /\ word.eqb out (word.of_Z 0)
                    = negb (is_flag_set status AES_STATUS_OUTPUT_VALID)).


  Lemma aes_data_valid_correct :
    program_logic_goal_for_function! aes_data_valid.
  Proof.
    (* initial processing *)
    repeat straightline.

    read_status.
    repeat straightline.

    (* done; prove postcondition *)
    do 3 eexists. ssplit; eauto; [ ].
    subst_lets. cbv [is_flag_set].
    boolsimpl. reflexivity.
  Qed.

  Global Instance spec_of_aes_idle : spec_of aes_idle :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) (s : state),
        (* no special requirements of the memory *)
        R m ->
        (* no constraints on current state *)
        execution tr s ->
        let args := [] in
        call function_env aes_idle tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                exists (status out : Semantics.word) (s' : state),
                  (* trace has exactly one new read value *)
                  tr' = (map.empty, READ, [AES_STATUS],(map.empty,[status])) :: tr
                  (* ...and there is a new state matching the new trace *)
                  /\ execution tr' s'
                  (* ...and all the same properties as before hold on the memory *)
                  /\ R m'
                  (* ...and there is one output value *)
                  /\ rets = [out]
                  (* ...and the output value is zero if and only if the idle
                     flag is unset *)
                  /\ word.eqb out (word.of_Z 0)
                    = negb (is_flag_set status AES_STATUS_IDLE)).


  Lemma aes_idle_correct :
    program_logic_goal_for_function! aes_idle.
  Proof.
    (* initial processing *)
    repeat straightline.

    read_status.
    repeat straightline.

    (* done; prove postcondition *)
    do 3 eexists. ssplit; eauto; [ ].
    subst_lets. cbv [is_flag_set].
    boolsimpl. reflexivity.
  Qed.

  Global Instance spec_of_aes_init : spec_of aes_init :=
    fun function_env =>
      forall s (tr : trace) (m : mem) (R : _ -> Prop)
        aes_cfg_operation aes_cfg_mode aes_cfg_key_len
        aes_cfg_manual_operation,
        (* no special requirements of the memory *)
        R m ->
        (* circuit must start in UNINITIALIZED or IDLE state *)
        execution tr s ->
        match s with
        | UNINITIALIZED => True
        | IDLE _ => True
        | _ => False
        end ->
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
                    execution tr' (IDLE (map.put (get_known_regs s) AES_CTRL ctrl))
                    /\ ctrl_operation ctrl = negb (word.eqb aes_cfg_operation (word.of_Z 0))
                    /\ ctrl_mode ctrl = aes_cfg_mode
                    /\ ctrl_key_len ctrl = aes_cfg_key_len
                    /\ ctrl_manual_operation ctrl
                      = negb (word.eqb aes_cfg_manual_operation (word.of_Z 0)))
                (* ...and the same properties as before hold on the memory *)
                /\ R m'
                (* ...and there is no output *)
                /\ rets = []).


  Lemma aes_init_correct :
    program_logic_goal_for_function! aes_init.
  Proof.
    (* initial processing *)
    repeat straightline.

    write_control.
    repeat straightline.

    (* simplify post-write guarantees *)
    cbn [write_step reg_category] in *.

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
               pose proof has_size_nonneg _ _ H
           end.

    simplify_implicits.

    (* split cases *)
    eexists; ssplit.
    { (* prove that the execution trace is OK *)
      destruct_one_match_hyp; try contradiction;
        subst; eassumption. }
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

  Global Instance spec_of_aes_key_put : spec_of aes_key_put :=
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

  (* TODO: move *)
  Lemma map_putmany_of_list_zip_snoc {key value} {map : map.map key value}
        ks vs k v m m' :
    map.putmany_of_list_zip (map:=map) ks vs m = Some m' ->
    map.putmany_of_list_zip (ks ++ [k]) (vs ++ [v]) m = Some (map.put m' k v).
  Proof.
    revert vs k v m m'; induction ks; destruct vs;
      [ cbn; congruence | discriminate | discriminate | ].
    intros. rewrite <-!app_comm_cons. cbn [map.putmany_of_list_zip].
    auto.
  Qed.

  (* TODO: move *)
  Lemma nth_firstn {A} (l : list A) i n d :
    (i < n)%nat -> nth i (firstn n l) d = nth i l d.
  Proof.
    revert l i d. induction n; [ lia | ].
    destruct l; [ reflexivity | ].
    destruct i; [ reflexivity | ].
    cbn [firstn nth]; intros.
    apply IHn. lia.
  Qed.

  Lemma aes_key_put_correct :
    program_logic_goal_for_function! aes_key_put.
  Proof.
    (* we want to avoid letting [straightline] go too far here, so we can apply
       [cond_nobreak], which requires a [seq] in front of [cond] *)
    do 2 straightline. repeat straightline_cleanup.
    simplify_implicits.

    (* setup: assert useful facts and simplify hypotheses *)
    (* assert that key length enum members are unique *)
    pose proof enum_unique aes_key_len as key_len_unique.
    simplify_unique_words_in key_len_unique.

    (* key_len must be one of the members of the aes_key_len enum *)
    lazymatch goal with
    | H : enum_member aes_key_len ?len |- _ =>
      cbn [enum_member aes_key_len In] in H
    end.

    (* this assertion helps prove that i does not get truncated *)
    assert (9 < 2 ^ Semantics.width) by (cbn; lia).
    pose proof nregs_key_eq.

    (* upper bound key_len *)
    assert (4 <= length key_arr <= 8)%nat.
    { lazymatch goal with H : length key_arr = _ |- _ => rewrite H end.
      repeat destruct_one_match; lia. }

    (* setup done; now we can proceed with the program logic *)

    (* after the conditional, num_regs_key_used is set *)
    apply cond_nosplit with
        (post_cond :=
           fun tr' m' l' =>
             tr' = tr /\ m' = m
             /\ l' = map.put l "num_regs_key_used"
                            (word.of_Z (Z.of_nat (length key_arr)))).

    { (* prove that the conditional statement fulfills its postcondition *)
      (* destruct branches *)
      split_if; [ | intros; split_if ]; intros;
        repeat lazymatch goal with
               | H : word.unsigned _ <> 0 |- _ =>
                 apply word.if_nonzero, word.eqb_true in H
               | H : word.unsigned _ = 0 |- _ =>
                 apply word.if_zero, word.eqb_false in H
               end; subst.
      (* destruct nonsensical cases *)
      all:repeat (destruct_one_match_hyp_of_type bool; try congruence);
        repeat lazymatch goal with
               | H : _ \/ _ |- _ => destruct H; try congruence
               end; [ ].
      all:repeat straightline.
      all:ssplit; [ reflexivity .. | ].
      all:apply f_equal; subst_lets; apply f_equal.
      all:lia. }

    repeat straightline.

    (* begin first while loop *)
    let l := lazymatch goal with |- cmd _ _ _ _ ?l _ => l end in
    apply atleastonce_localsmap
      with (v0:=length key_arr)
           (lt:=lt)
           (invariant:=
              fun v tr' m' l' =>
                (* the new state is the old one plus the first i keys *)
                (exists rs',
                    map.putmany_of_list_zip
                      (map (fun i => reg_addr (key_from_index i))
                           (seq 0 (length key_arr - v)))
                      (firstn (length key_arr - v) key_arr) rs = Some rs'
                    /\ execution (p:=state_machine_parameters) tr' (IDLE rs'))
                (* array accesses in bounds *)
                /\ (0 < v <= length key_arr)%nat
                (* locals are unaffected except for i *)
                /\ l' = map.put l "i" (word.of_Z (Z.of_nat (length key_arr - v)))
                (* memory is unaffected *)
                /\ (array scalar32 (word.of_Z 4) key_arr_ptr key_arr ⋆ R)%sep m').
    { apply lt_wf. }

    { (* case in which the loop breaks immediately (cannot happen) *)
      repeat straightline.
      exfalso.

      repeat lazymatch goal with
             | br := if word.ltu _ _ then _ else _,
                     H : word.unsigned br = 0 |- _ =>
                     assert (word.unsigned br <> 0);
                       [ subst br | congruence ]
             | H : length key_arr = _ |- context [length key_arr] =>
               rewrite H
             | |- context [word.eqb ?x ?y] => destr (word.eqb x y)
             | _ => progress push_unsigned
             end.
      all:destruct_one_match; lia. }

    { (* invariant holds at start of loop *)
      rewrite Nat.sub_diag.
      ssplit;
      lazymatch goal with
      | |- ?m = map.put ?m _ _ =>
        subst1_map m; rewrite map.put_put_same; reflexivity
      | |- sep _ _ _ => ecancel_assumption
      | |- (_ < _)%nat => lia
      | |- (_ <= _)%nat => lia
      | _ => idtac
      end.
      cbn [firstn]. eexists; split; [ reflexivity | ].
      eassumption. }

    { (* the body of the loop proves the invariant if it continues and the
         postcondition if it breaks *)
      repeat straightline.

      (* first, we need to find the separation-logic condition and isolate the
         key we will be loading *)

      (* assertion that matches one of the array_address_inbounds side
         conditions *)
      let i := lazymatch goal with
               | _ := map.put _ "i" (word.of_Z (Z.of_nat ?i)) |- _ => i end in
      let a := constr:(word.add key_arr_ptr (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4))) in
      let offset := constr:(word.sub a key_arr_ptr) in
      assert (i = Z.to_nat (word.unsigned offset / word.unsigned (width:=width) (word.of_Z 4))) as Hindex;
        [ ring_simplify offset | ].
      { push_unsigned. rewrite (Z.mul_comm 4), Z.div_mul by lia. lia. }

      (* rearrangement of Hindex for other side conditions  *)
      lazymatch type of Hindex with
      | ?i = Z.to_nat (word.unsigned ?offset / ?size) =>
        assert (word.unsigned offset = Z.of_nat i * size) as Hoffset;
          [ ring_simplify offset; push_unsigned; lia | ]
      end.

      let Hsep :=
          lazymatch goal with H : sep _ _ ?m |- cmd _ _ _ ?m _ _ => H end in
      pose proof Hsep;
      seprewrite_in @array_address_inbounds Hsep; [ | | exact Hindex | ];
        [ rewrite Hoffset; push_unsigned; lia
        | rewrite Hoffset; push_unsigned; apply Z.mod_mul; lia
        | ].

      (* seprewrite leaves an evar for a default key; fill it in *)
      match goal with
      | H : context [List.hd ?d ?l] |- _ =>
        is_evar d; unify (List.hd d l) (List.hd (word.of_Z 0) l)
      end.

      (* now, finally, we can process the loop body *)

      (* set key register *)
      write_key.

      (* rest of loop body *)
      repeat straightline.

      { (* "continue" case; prove invariant still holds *)
        cbv [Markers.split].
        lazymatch goal with
        | |- exists v, _ /\ (v < ?oldv)%nat => exists (oldv - 1)%nat; split; [ | lia ]
        end.

        (* simplify the loop-continue condition (i < length key_arr) *)
        match goal with
        | H : word.unsigned _ <> 0 |- _ =>
          apply word.if_nonzero in H;
            rewrite word.unsigned_ltu in H;
            apply Z.ltb_lt in H;
            rewrite word.unsigned_of_Z, word.wrap_small in H by lia
        end.
        lazymatch goal with
        | i := word.add _ (word.of_Z 1),
               H : word.unsigned i < _ |- _ =>
               subst i;
                 rewrite word.unsigned_add, word.unsigned_of_Z_1 in H;
                 rewrite ?word.unsigned_of_Z, ?word.wrap_small in H
                   by (rewrite ?word.wrap_small; lia)
        end.
        ssplit;
          lazymatch goal with
          | |- ?l' = map.put ?l _ _ =>
            subst1_map l';
              lazymatch goal with
              | |- map.put ?l' _ _ = _ =>
                subst1_map l'
              end;
              rewrite map.put_put_same;
              f_equal; apply word.unsigned_inj;
                push_unsigned; lia
          | |- sep _ _ _ => ecancel_assumption
          | |- (_ < _)%nat => lia
          | |- (_ <= _)%nat => lia
          | _ => idtac
          end.

        lazymatch goal with
        | |- context [(length key_arr - (?v - 1))%nat] =>
          replace (length key_arr - (v - 1))%nat
            with (S (length key_arr - v))%nat by lia
        end.
        rewrite !firstn_succ_snoc with (d:=word.of_Z 0) by length_hammer.
        eexists; ssplit; [ | eassumption ].
        autorewrite with pull_snoc natsimpl.
        rewrite !hd_skipn.
        auto using map_putmany_of_list_zip_snoc. }

      { (* "break" case; prove postcondition holds after the rest of the function *)

        (* simplify the loop-break condition (length key_arr <= i) *)
        match goal with
        | H : word.unsigned _ = 0 |- _ =>
          apply word.if_zero in H;
          rewrite word.unsigned_ltu in H;
            apply Z.ltb_ge in H;
            rewrite word.unsigned_of_Z, word.wrap_small in H by lia
        end.
        lazymatch goal with
        | H : Z.of_nat (length key_arr) <= word.unsigned ?i |- _ =>
          subst i; rewrite word.unsigned_add in H;
            autorewrite with push_unsigned in H;
            rewrite word.wrap_small in H by lia
        end.

        (* begin second while loop *)
        let l := lazymatch goal with |- cmd _ _ _ _ ?l _ => l end in
        unfold1_cmd_goal; cbn [cmd_body]; exists nat, lt;
        (* invariant *)
        exists (fun v tr' m' l' =>
             (* the new state is the old one plus the first i keys *)
             (exists rs',
                 map.putmany_of_list_zip
                   (map (fun i => reg_addr (key_from_index i))
                        (seq 0 (8 - v)))
                   (key_arr ++ repeat (word.of_Z 0) (8 - v - length key_arr))
                   rs = Some rs'
                 /\ execution (p:=state_machine_parameters) tr' (IDLE rs'))
             (* bounds for # iterations *)
             /\ (v <= 8 - length key_arr)%nat
             (* locals are unaffected except for i *)
             /\ l' = map.put l "i" (word.of_Z (Z.of_nat (8 - v)))
             (* memory is unaffected *)
             /\ (array scalar32 (word.of_Z 4) key_arr_ptr key_arr ⋆ R)%sep m').
        ssplit.
        { apply lt_wf. }
        { (* invariant holds at loop start *)
          exists (8 - length key_arr)%nat. (* total # iterations *)
          replace (8 - (8 - length key_arr))%nat with (length key_arr) by lia.
          rewrite Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
          ssplit;
          lazymatch goal with
            | |- ?m = map.put ?m _ _ =>
              subst1_map m; rewrite map.put_put_same; reflexivity
            | |- sep _ _ _ => ecancel_assumption
            | |- (_ < _)%nat => lia
            | |- (_ <= _)%nat => lia
            | _ => idtac
          end.

          eexists; ssplit; [ | eassumption ].

          assert (v = 1)%nat by lia.
          lazymatch goal with
          | H : map.putmany_of_list_zip (map ?f (seq 0 ?n)) (firstn ?n ?vs) _ = Some _
            |- context [map.putmany_of_list_zip ?ks ?vs ?m] =>
            replace (map.putmany_of_list_zip ks vs m)
              with (map.putmany_of_list_zip
                      (map f (seq 0 (S n))) (firstn (S n) vs) m)
                   by (autorewrite with push_firstn;
                       repeat (f_equal; try lia))
          end.
          autorewrite with pull_snoc natsimpl.
          rewrite firstn_succ_snoc with (d:=word.of_Z 0) by length_hammer.
          rewrite hd_skipn.
          eauto using map_putmany_of_list_zip_snoc. }

        { (* the body of the loop proves the invariant if it continues and the
             postcondition if it breaks *)
          repeat straightline.
          split; intros.

          { (* prove that the invariant holds after the loop body *)

            (* simplify the loop-continue condition (i < 8) *)
            match goal with
            | H : word.unsigned _ <> 0 |- _ =>
              apply word.if_nonzero in H;
                rewrite word.unsigned_ltu in H;
                apply Z.ltb_lt in H;
                rewrite nregs_key_eq in H;
                autorewrite with push_unsigned in H
            end.

            repeat straightline.

            (* set key register *)
            write_key.

          (* rest of loop body *)
          repeat straightline.

          (* loop body done; prove invariant still holds *)

          (* provide new measure *)
          lazymatch goal with
          | |- exists v, _ /\ (v < ?oldv)%nat => exists (oldv - 1)%nat; split; [ | lia ]
          end.

          (* handle most invariant cases *)
          ssplit;
            lazymatch goal with
            | |- ?l' = map.put ?l _ _ =>
              subst1_map l';
                lazymatch goal with
                | |- map.put ?l' _ _ = _ =>
                  subst1_map l'
                end;
                rewrite map.put_put_same;
                f_equal; apply word.unsigned_inj;
                  subst_lets; push_unsigned; lia
            | |- sep _ _ _ => ecancel_assumption
            | |- ?G => tryif is_lia G then lia else idtac
            end.

          (* final invariant case: new register state *)

          (* arithmetic simplification *)
          lazymatch goal with
          | |- context [(8 - (?v - 1))%nat] =>
            replace (8 - (v - 1))%nat
              with (S (8 - v))%nat by lia
          end.
          rewrite (Nat.sub_succ_l (length key_arr) (8 - _)%nat) by lia.

          (* list simplifications *)
          cbn [repeat]. rewrite repeat_cons, app_assoc.
          autorewrite with pull_snoc.

          (* solve *)
          simplify_implicits.
          eexists; ssplit; [ | eassumption ].
          eauto using map_putmany_of_list_zip_snoc. }

          { (* post-loop; given invariant and loop-break condition, prove
               postcondition holds after the rest of the function *)

            repeat straightline.

            (* simplify the loop-break condition (8 <= i) *)
            match goal with
            | H : word.unsigned _ = 0 |- _ =>
              apply word.if_zero in H;
              rewrite word.unsigned_ltu in H;
              apply Z.ltb_ge in H;
              rewrite nregs_key_eq in H;
              autorewrite with push_unsigned in H
            end.

            eexists; ssplit; eauto; [ ].
            eexists; ssplit; eauto; [ ].
            lazymatch goal with
            | H : map.putmany_of_list_zip ?ks1 ?vs1 ?m = Some ?m'
              |- map.putmany_of_list_zip ?ks2 ?vs2 ?m = Some ?m' =>
              replace ks2 with ks1;
                [ replace vs2 with vs1; [ exact H | ] | ]
            end.
            { repeat (f_equal; try lia). }
            { lazymatch goal with |- context [(8-?v)%nat] =>
                                  assert (v = 0)%nat by lia end.
              subst. reflexivity. } } } } }
  Qed.

  Global Instance spec_of_aes_iv_put : spec_of aes_iv_put :=
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
    (* intial processing *)
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
    write_iv_n 0%nat. repeat straightline.

    (* i = 1 *)
    split; repeat straightline; [ dexpr_hammer | ].
    write_iv_n 1%nat; [ simplify_implicits; subst_lets; ring | ].
    repeat straightline.

    (* i = 2 *)
    split; repeat straightline; [ dexpr_hammer | ].
    write_iv_n 2%nat; [ simplify_implicits; subst_lets; ring | ].
    repeat straightline.

    (* i = 3 *)
    split; repeat straightline; [ dexpr_hammer | ].
    write_iv_n 3%nat; [ simplify_implicits; subst_lets; ring | ].
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

  Global Instance spec_of_aes_data_put : spec_of aes_data_put :=
    fun function_env =>
      forall (tr : trace) (m : mem) R
        (rs : known_register_state)
        (data_ptr data0 data1 data2 data3 : Semantics.word),
        (* data array is in memory *)
        (array scalar32 (word.of_Z 4) data_ptr [data0;data1;data2;data3] * R)%sep m ->
        (* circuit must be in IDLE state *)
        execution tr (IDLE rs) ->
        (* the key and iv registers must be populated *)
        nregs_populated rs KeyReg = 8%nat ->
        nregs_populated rs IVReg = 4%nat ->
        (* the data registers must *not* be populated *)
        nregs_populated rs DataInReg = 0%nat ->
        let args := [data_ptr] in
        call function_env aes_data_put tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                exists exp_out,
                  (* the circuit is now in the BUSY state *)
                  execution tr' (BUSY (unset_inp_regs rs) exp_out
                                      timing.ndelays_core)
                  (* ...and the expected output matches the AES spec for this data *)
                  /\ aes_expected_output
                      (map.putmany_of_list
                         [(reg_addr DATA_IN0, data0)
                          ; (reg_addr DATA_IN1, data1)
                          ; (reg_addr DATA_IN2, data2)
                          ; (reg_addr DATA_IN3, data3)] rs) = Some exp_out
                  (* ...and the same properties as before hold on the memory *)
                  /\ (array scalar32 (word.of_Z 4) data_ptr [data0;data1;data2;data3] * R)%sep m'
                  (* ...and there is no output *)
                  /\ rets = []).

  Definition data_in_from_index (i : nat) : Register :=
    nth i [DATA_IN0;DATA_IN1;DATA_IN2;DATA_IN3] CTRL.

  Lemma data_in_from_index_category i :
    (i < 4)%nat -> reg_category (data_in_from_index i) = DataInReg.
  Proof.
    intros. cbv [data_in_from_index].
    apply Forall_nth; [ | length_hammer ].
    repeat constructor.
  Qed.

  Lemma all_regs_in_category_complete c r :
    reg_category r = c -> In r (all_regs_in_category c).
  Proof.
    destruct c, r; cbn [reg_category]; try discriminate; intros;
      cbn; tauto.
  Qed.

  (* TODO: move *)
  Lemma length_filter_le {A} (f : A -> bool) l :
    (length (filter f l) <= length l)%nat.
  Proof.
    induction l; cbn [filter length]; [ lia | ].
    destruct_one_match; length_hammer.
  Qed.

  (* TODO: move *)
  Lemma filter_noop_forallb {A} (f : A -> bool) l :
    length (filter f l) = length l <-> forallb f l = true.
  Proof.
    induction l; intros; [ cbn; tauto | ].
    cbn [filter forallb].
    destruct_one_match; cbn [andb length];
      [ rewrite <-IHl; lia | ].
    split; try discriminate; [ ].
    pose proof (length_filter_le f l).
    lia.
  Qed.

  Lemma nregs_populated_full rs c :
    nregs_populated rs c = length (all_regs_in_category c) ->
    forall r, reg_category r = c -> reg_lookup rs r <> None.
  Proof.
    cbv [nregs_populated]. rewrite filter_noop_forallb.
    rewrite forallb_forall. intros Hlookup; intros.
    specialize (Hlookup _ ltac:(eauto using all_regs_in_category_complete)).
    destruct_one_match_hyp; congruence.
  Qed.

  Lemma aes_expected_output_exists rs :
    nregs_populated rs ControlReg = 1%nat ->
    nregs_populated rs KeyReg = 8%nat ->
    nregs_populated rs IVReg = 4%nat ->
    nregs_populated rs DataInReg = 4%nat ->
    aes_expected_output rs <> None.
  Proof.
    intros.
    cbv [aes_expected_output option_bind].
    repeat
      (destruct_one_match;
       [ | repeat
             lazymatch goal with
             | H : reg_lookup _ _ = None |- None <> None =>
               exfalso; eapply nregs_populated_full;
               [ | solve [eauto] .. ]; cbn [reg_category]
             | H : nregs_populated ?rs ?c = _
               |- context [nregs_populated ?rs ?c] =>
               rewrite H; reflexivity
             end ]).
    repeat destruct_pair_let. congruence.
  Qed.

  Lemma nregs_populated_put rs r v cat :
    nregs_populated (map.put rs (reg_addr r) v) cat =
    if reg_category_eqb cat (reg_category r)
    then match reg_lookup rs r with
         | None => S (nregs_populated rs cat)
         | Some _ => nregs_populated rs cat
         end
    else nregs_populated rs cat.
  Proof.
    cbv [nregs_populated reg_lookup].
    destruct cat.
    all:cbn.
    { destruct r; cbn [reg_category reg_addr].
      { rewrite map.get_put_same.
        destruct_one_match; reflexivity. }

      destr (reg_category r);
        lazymatch goal with
          | H : reg_category _ = _ |- _ =>
            apply all_regs_in_category_complete in H;
              cbn in H
        end.
      2:{
        rewrite map.get_put_diff.
        Check all_regs_in_category_complete.
        2:{
      destruct r; cbn [reg_category reg_addr].
      { rewrite map.get_put_dec.
        rewrite word.eqb_refl.
    cbv [nregs_populated reg_lookup]. intros.
    rewrite map.fold_put; auto.
    { rewrite addr_in_category_reg_addr. reflexivity. }
    { intros. repeat destruct_one_match; reflexivity. }
  Qed.

  (* if the circuit is in any state except UNINITIALIZED, the control register
     must exist *)
  Lemma control_register_exists t s :
    s <> UNINITIALIZED ->
    execution t s ->
    nregs_populated (get_known_regs s) ControlReg = 1%nat.
  Proof.
    revert s; induction t; [ cbn; congruence | ].
    intros. cbn [execution] in *. destruct_products.
    cbv [step] in *.
    cbn [parameters.write_step
           parameters.read_step state_machine_parameters] in *.
    cbv [read_step write_step] in *.
    repeat lazymatch goal with
           | H : False |- _ => contradiction H
           | _ => destruct_one_match_hyp;
                   logical_simplify; subst
           end.
    all:cbn [get_known_regs].
  Qed.

  Lemma interact_write_data_in i call addre vale t m l
        (post : trace -> mem -> locals -> Prop) rs addr val :
    dexprs m l [addre; vale] [addr; val] ->
    addr = word.add AES_DATA_IN0 (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4)) ->
    (i < 4)%nat ->
    nregs_populated rs KeyReg = 8%nat ->
    nregs_populated rs IVReg = 4%nat ->
    (nregs_populated rs DataInReg < 4)%nat ->
    execution t (IDLE rs) ->
    (forall s',
        write_step (IDLE rs) (data_in_from_index i) val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t) s' ->
        post ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t)
             m l) ->
    cmd call (cmd.interact [] WRITE [addre;vale]) t m l post.
  Proof.
    intros; eapply interact_write; intros; infer;
      cbv [parameters.write_step state_machine_parameters] in *;
      eauto.
    { repeat (destruct i; try lia); subst; cbn; ring. }
    { cbv [write_step]. rewrite data_in_from_index_category by lia.
      exists (IDLE rs). destruct_one_match.
      1:{ rewrite nregs_populated_put. lia.
      destruct_one_match; [ | solve [eexists; eauto] ].
      eexists.
      Search nregs_populated.
      2: eauto 10.
      Search aes_expected_output.
      exists (match s with
      do 2 eexists; ssplit; eauto.
      cbn beta iota. ssplit; try eauto.
      destruct_one_match.
      2:reflexivity.
      exists (IDLE rs). eexists; ssplit; eauto. }
  Qed.
  Lemma interact_write_data_in i call addre vale t m l
        (post : trace -> mem -> locals -> Prop) rs addr val :
    dexprs m l [addre; vale] [addr; val] ->
    addr = word.add AES_DATA_IN0 (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4)) ->
    (i < 4)%nat ->
    nregs_populated rs KeyReg = 8%nat ->
    nregs_populated rs IVReg = 4%nat ->
    (nregs_populated rs DataInReg < 4)%nat ->
    execution t (IDLE rs) ->
    (forall s',
        write_step (IDLE rs) (data_in_from_index i) val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t) s' ->
        post ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t)
             m l) ->
    cmd call (cmd.interact [] WRITE [addre;vale]) t m l post.
  Proof.
    intros; eapply interact_write; intros; infer;
      cbv [parameters.write_step state_machine_parameters] in *;
      eauto.
    { repeat (destruct i; try lia); subst; cbn; ring. }
    { cbv [write_step]. rewrite data_in_from_index_category by lia.
      exists (IDLE rs). destruct_one_match; [ | solve [eexists; eauto] ].
      eexists.
      Search nregs_populated.
      2: eauto 10.
      Search aes_expected_output.
      exists (match s with
      do 2 eexists; ssplit; eauto.
      cbn beta iota. ssplit; try eauto.
      destruct_one_match.
      2:reflexivity.
      exists (IDLE rs). eexists; ssplit; eauto. }
  Qed.
  Local Ltac write_data_in_n n :=
    eapply interact_write_data_in with (i:=n);
    [ try post_interaction ..
    | intros;
      try lazymatch goal with
          | H : write_step _ _ _ _ |- _ =>
            cbv [write_step] in H;
            rewrite data_in_from_index_category in H by lia; subst
          end ].

  Lemma aes_data_put_correct :
    program_logic_goal_for_function! aes_data_put.
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
    pose proof nregs_data_eq.

    (* unroll while loop *)
    eapply unroll_while with (iterations:=4%nat). cbn [repeat_logic_step].
    repeat straightline.

    (* process each iteration of the while loop *)

    (* i = 0 *)
    split; repeat straightline; [ dexpr_hammer | ].
    interaction_with_reg DATA_IN0.
    infer; subst; clear_old_executions.
    repeat straightline.


    (* i = 1 *)
    split; repeat straightline; [ dexpr_hammer | ].
    interaction_with_reg DATA_IN1.
    infer; subst; clear_old_executions.
    repeat straightline.

    (* i = 2 *)
    split; repeat straightline; [ dexpr_hammer | ].
    interaction_with_reg DATA_IN2.
    infer; subst; clear_old_executions.
    repeat straightline.

    (* i = 3 *)
    split; repeat straightline; [ dexpr_hammer | ].
    interaction_with_reg DATA_IN3.
    infer; subst; clear_old_executions.
    repeat straightline.

    (* i = 4; loop done *)
    ssplit; repeat straightline; [ dexpr_hammer | ].

    (* done; prove postcondition *)
    cbn [array].
    repeat match goal with
           | |- context [scalar32 ?addr] =>
             progress ring_simplify addr
           end.

    eexists; ssplit; eauto; [ ].
    (* find and apply execution hypothesis by asserting states are equal *)
    lazymatch goal with H : execution ?t ?s1 |- execution ?t ?s2 =>
                        let H' := fresh in
                        assert (s2 = s1) as H'; [ | rewrite H'; apply H ]
    end.
    rewrite !unset_inp_regs_put. reflexivity.
  Qed.

  (* TODO: the real state machine is slightly more complex; AES block can get
     input while BUSY and stalls in BUSY state until output is read. The spec
     should be modified to account for this behavior. For now, this spec is
     exactly the same as aes_data_put. *)
  Global Instance spec_of_aes_data_put_wait : spec_of aes_data_put_wait :=
    fun function_env =>
      forall (tr : trace) (m : mem) R
        (rs : known_register_state)
        (data_ptr data0 data1 data2 data3 : Semantics.word),
        (* data array is in memory *)
        (array scalar32 (word.of_Z 4) data_ptr [data0;data1;data2;data3] * R)%sep m ->
        (* circuit must be in IDLE state *)
        execution tr (IDLE rs) ->
        (* the key and iv registers must be populated *)
        nregs_populated rs KeyReg = 8%nat ->
        nregs_populated rs IVReg = 4%nat ->
        (* the data registers must *not* be populated *)
        nregs_populated rs DataInReg = 0%nat ->
        let args := [data_ptr] in
        call function_env aes_data_put_wait tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                exists exp_out,
                  (* the circuit is now in the BUSY state *)
                  execution tr' (BUSY (unset_inp_regs rs) exp_out
                                      timing.ndelays_core)
                  (* ...and the expected output matches the AES spec for this data *)
                  /\ aes_expected_output
                      (map.putmany_of_list
                         [(reg_addr DATA_IN0, data0)
                          ; (reg_addr DATA_IN1, data1)
                          ; (reg_addr DATA_IN2, data2)
                          ; (reg_addr DATA_IN3, data3)] rs) = Some exp_out
                  (* ...and the same properties as before hold on the memory *)
                  /\ (array scalar32 (word.of_Z 4) data_ptr [data0;data1;data2;data3] * R)%sep m'
                  (* ...and there is no output *)
                  /\ rets = []).

  Lemma aes_data_put_wait_correct :
    program_logic_goal_for_function! aes_data_put_wait.
  Proof.
    (* initial processing *)
    repeat straightline.
    simplify_implicits.

    (* we know the circuit is in IDLE state, so loop has exactly 1 iteration *)
    eapply unroll_while with (iterations:=1%nat). cbn [repeat_logic_step].
    repeat straightline.

    split; repeat straightline; [ dexpr_hammer; congruence | ].

    (* Call aes_data_ready *)
    straightline_call; eauto; [ ].

    (* simplify guarantees *)
    logical_simplify; subst.
    lazymatch goal with
    | H : execution (_ :: _) _ |- _ =>
      pose proof H; apply invert1_execution in H; logical_simplify
    end.
    invert_step; subst.
    cbn [parameters.reg_addr parameters.write_step parameters.read_step
                             state_machine_parameters] in *.
    infer; subst.
    (* assert that the register address we just read is STATUS *)
    lazymatch goal with
    | H : reg_addr ?r = AES_STATUS |- _ =>
      apply (reg_addr_unique r STATUS) in H; subst
    end.
    cbv [status_matches_state] in *. simplify_implicits.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H; destruct H
           | H : word.eqb _ _ = _ |- _ => apply word.eqb_false in H
           | H : is_flag_set _ _  = _ |- _ => progress rewrite H in *
           end.

    (* loop done *)
    repeat straightline.
    split; repeat straightline; [ dexpr_hammer; try congruence; reflexivity | ].
    split; repeat straightline; [ dexpr_hammer | ].

    (* call aes_data_put *)
    straightline_call; eauto; [ ].

    (* simplify guarantees *)
    logical_simplify; subst.

    (* done; prove postcondition *)
    repeat straightline. eauto.
  Qed.

  Global Instance spec_of_aes_data_get : spec_of aes_data_get :=
    fun function_env =>
      forall (tr : trace) (m : mem) R
        (rs : known_register_state)
        (data_ptr data0 data1 data2 data3 : Semantics.word),
        (* data array is in memory, with arbitrary values *)
        (array scalar32 (word.of_Z 4) data_ptr [data0;data1;data2;data3] * R)%sep m ->
        (* circuit must be in the DONE state *)
        execution tr (DONE rs) ->
        (* the output data registers must be populated *)
        nregs_populated rs DataOutReg = 4%nat ->
        let args := [data_ptr] in
        call function_env aes_data_get tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                exists out0 out1 out2 out3,
                  (* the circuit is now in the IDLE state with output registers unset *)
                  execution tr' (IDLE (map.remove
                                         (map.remove
                                            (map.remove
                                               (map.remove rs
                                                           (reg_addr DATA_OUT0))
                                               (reg_addr DATA_OUT1))
                                            (reg_addr DATA_OUT2))
                                         (reg_addr DATA_OUT3)))
                  (* ...and the array now holds the values from the output registers *)
                  /\ (array scalar32 (word.of_Z 4) data_ptr [out0;out1;out2;out3] * R)%sep m'
                  /\ reg_lookup rs DATA_OUT0 = Some out0
                  /\ reg_lookup rs DATA_OUT1 = Some out1
                  /\ reg_lookup rs DATA_OUT2 = Some out2
                  /\ reg_lookup rs DATA_OUT3 = Some out3
                  (* ...and there are no return values *)
                  /\ rets = []).

  Lemma aes_data_get_correct :
    program_logic_goal_for_function! aes_data_get.
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
    pose proof nregs_data_eq.

    (* unroll while loop *)
    eapply unroll_while with (iterations:=4%nat). cbn [repeat_logic_step].
    repeat straightline.

    (* process each iteration of the while loop *)

    (* i = 0 *)
    split; repeat straightline; [ dexpr_hammer | ].

    (* read register *)
    interaction_with_reg DATA_OUT0.
    infer; subst; clear_old_executions.
    repeat straightline.

    (* store result in memory *)
    simplify_implicits.
    ring_simplify_store_addr.
    (* the following line is in [straightline] but needs simplify_implicits for
       it to work *)
    eapply store_four_of_sep_32bit;
      [ reflexivity | simplify_implicits; solve [ ecancel_assumption ] |  ].
    repeat straightline.

    (* i = 1 *)
    split; repeat straightline; [ dexpr_hammer | ].

    (* read register *)
    interaction_with_reg DATA_OUT1.
    infer; subst; clear_old_executions.
    repeat straightline.

    (* store result in memory *)
    simplify_implicits.
    ring_simplify_store_addr.
    (* the following line is in [straightline] but needs simplify_implicits for
       it to work *)
    eapply store_four_of_sep_32bit;
      [ reflexivity | simplify_implicits; solve [ ecancel_assumption ] |  ].
    repeat straightline.

    (* i = 2 *)
    split; repeat straightline; [ dexpr_hammer | ].

    (* read register *)
    interaction_with_reg DATA_OUT2.
    infer; subst; clear_old_executions.
    repeat straightline.

    (* store result in memory *)
    simplify_implicits.
    ring_simplify_store_addr.
    (* the following line is in [straightline] but needs simplify_implicits for
       it to work *)
    eapply store_four_of_sep_32bit;
      [ reflexivity | simplify_implicits; solve [ ecancel_assumption ] |  ].
    repeat straightline.

    (* i = 3 *)
    split; repeat straightline; [ dexpr_hammer | ].

    (* read register *)
    interaction_with_reg DATA_OUT3.
    infer; subst; clear_old_executions.
    repeat straightline.

    (* store result in memory *)
    simplify_implicits.
    ring_simplify_store_addr.
    (* the following line is in [straightline] but needs simplify_implicits for
       it to work *)
    eapply store_four_of_sep_32bit;
      [ reflexivity | simplify_implicits; solve [ ecancel_assumption ] |  ].
    repeat straightline.

    (* i = 4; loop done *)
    ssplit; repeat straightline; [ dexpr_hammer | ].

    (* done; prove postcondition *)
    cbn [array].
    repeat match goal with
           | |- context [scalar32 ?addr] =>
             progress ring_simplify addr
           end.

    (* change register lookups to refer to original register state *)
    repeat lazymatch goal with
           | H : reg_lookup (map.remove _ _) _ = Some _ |- _ =>
             cbv [reg_lookup] in H;
               rewrite !map.get_remove_dec in H;
               rewrite !word.eqb_ne in H by (apply reg_addr_neq; congruence)
           end.

    do 4 eexists; ssplit; eauto; [ ].
    simplify_implicits.
    ecancel_assumption.
  Qed.

  Definition output_matches_state out s :=
    match s with
    | DONE rs =>
      reg_lookup rs DATA_OUT0 = Some out.(data_out0)
      /\ reg_lookup rs DATA_OUT1 = Some out.(data_out1)
      /\ reg_lookup rs DATA_OUT2 = Some out.(data_out2)
      /\ reg_lookup rs DATA_OUT3 = Some out.(data_out3)
    | BUSY _ exp_output _ => exp_output = out
    | _ => False
    end.

  Definition get_register_state s : known_register_state :=
    match s with
    | DONE rs => rs
    | BUSY rs _ _ => rs
    | IDLE rs => rs
    | UNINITIALIZED => map.empty
    end.

  Global Instance spec_of_aes_data_get_wait : spec_of aes_data_get_wait :=
    fun function_env =>
      forall (tr : trace) (m : mem) R
        (out : aes_output)
        (data_ptr data0 data1 data2 data3 : Semantics.word) (s : state),
        (* data array is in memory, with arbitrary values *)
        (array scalar32 (word.of_Z 4) data_ptr [data0;data1;data2;data3] * R)%sep m ->
        (* circuit must be in the DONE or BUSY state (otherwise we can't prove
           termination) and expected or already-written output matches out *)
        execution tr s ->
        output_matches_state out s ->
        let args := [data_ptr] in
        call function_env aes_data_get_wait tr m (aes_globals ++ args)
             (fun tr' m' rets =>
                (* the circuit is now in the IDLE state with output registers unset *)
                execution tr' (IDLE (map.remove
                                       (map.remove
                                          (map.remove
                                             (map.remove (get_register_state s)
                                                         (reg_addr DATA_OUT0))
                                             (reg_addr DATA_OUT1))
                                          (reg_addr DATA_OUT2))
                                       (reg_addr DATA_OUT3)))
                (* ...and the array now holds the values from the expected output *)
                /\ (array scalar32 (word.of_Z 4) data_ptr
                         [out.(data_out0)
                          ; out.(data_out1)
                          ; out.(data_out2)
                          ; out.(data_out3)] * R)%sep m'
                (* ...and there are no return values *)
                /\ rets = []).

  Lemma unset_inp_regs_ignores_outregs rs out :
    aes_expected_output rs = Some out ->
    nregs_populated (unset_inp_regs rs) DataOutReg = nregs_populated rs DataOutReg.
  Proof.
    cbv [unset_inp_regs]. cbv [aes_expected_output option_bind].
    repeat (destruct_one_match; try congruence); [ ]. intros.
    repeat (erewrite nregs_populated_remove
             by (cbv [reg_lookup];
                 rewrite ?map.get_remove_diff by (apply reg_addr_neq; congruence);
                 eassumption);
            cbn [reg_category reg_category_eqb]).
    reflexivity.
  Qed.

  Lemma map_remove_put_same m k v :
    map.remove (map:=parameters.regs) (map.put m k v) k = map.remove m k.
  Proof.
    apply map.map_ext; intros.
    rewrite ?map.get_remove_dec, ?map.get_put_dec;
      destruct_one_match; subst; reflexivity.
  Qed.

  Lemma map_remove_put_diff m k1 k2 v :
    k1 <> k2 ->
    map.remove (map:=parameters.regs) (map.put m k1 v) k2 = map.put (map.remove m k2) k1 v.
  Proof.
    intros. apply map.map_ext; intros.
    rewrite ?map.get_remove_dec, ?map.get_put_dec, ?map.get_remove_dec;
      repeat destruct_one_match; subst; congruence.
  Qed.

  (* if a put causes more registers to be populated, then the put must set a
     register that was not previously set *)
  Lemma nregs_populated_increase rs r v c :
    (nregs_populated rs c
     < nregs_populated (map.put rs (reg_addr r) v) c)%nat ->
    reg_lookup rs r = None.
  Proof.
    cbv [nregs_populated reg_lookup]. intros.
    destr (map.get rs (reg_addr r)); [ exfalso | reflexivity ].
    erewrite map.fold_remove with (m:=rs) (k:=reg_addr r) in H;
      [ | intros; repeat destruct_one_match; reflexivity | eassumption ].
    erewrite map.fold_remove
      with (m:=map.put rs _ _) (k:=reg_addr r) in H;
      [ | intros; repeat destruct_one_match; reflexivity
        | apply map.get_put_same ].
    rewrite map_remove_put_same in *.
    destruct_one_match_hyp; lia.
  Qed.

  Lemma nregs_populated_set_out_regs rs out :
    nregs_populated (set_out_regs rs out) DataOutReg = 4%nat.
  Proof.
    cbv [set_out_regs nregs_populated].
    repeat match goal with
           | |- context [map.put _ ?key] =>
             erewrite map.fold_remove with (k:=key);
               [ | intros; repeat destruct_one_match; reflexivity
                 | rewrite ?map.get_remove_diff, ?map.get_put_diff
                   by (apply reg_addr_neq; congruence);
                   apply map.get_put_same ];
               rewrite addr_in_category_reg_addr; cbn [reg_category reg_category_eqb];
                 rewrite ?map_remove_put_diff by (apply reg_addr_neq; congruence);
                 rewrite map_remove_put_same
           end.
    repeat apply (f_equal S).
    lazymatch goal with
    | |- map.fold ?f ?r0 ?m = _ =>
      let H' := fresh in
      pose proof map.fold_to_list f r0 m as H';
        destruct H' as [l [Heq Hin] ]; rewrite Heq;
          rewrite <-(rev_involutive l)
    end.
    rewrite fold_left_rev_right.
    eapply fold_left_invariant with (I:= eq 0%nat); auto; [ ].
    intros. destruct_products; subst.
    repeat lazymatch goal with
           | H : In _ (rev _) |- _ => rewrite <-in_rev in H
           | H : In (?k,?v) ?l |- _ => apply Hin in H
           | H : context [map.get (map.remove _ _)] |- _ =>
             rewrite map.get_remove_dec in H
           end.
    repeat (destruct_one_match_hyp; try congruence).
    cbv [addr_in_category].
    cbn [all_regs existsb reg_category reg_category_eqb].
    boolsimpl. destruct_one_match; try reflexivity; [ ].
    repeat lazymatch goal with
           | H : (_ || _)%bool = true |- _ => apply Bool.orb_true_iff in H; destruct H
           | H : word.eqb _ _ = true |- _ => apply word.eqb_true in H
           | _ => congruence
           end.
  Qed.

  Lemma output_matches_state_set_out_regs rs out :
    output_matches_state out (DONE rs) ->
    set_out_regs rs out = rs.
  Proof.
    cbv [output_matches_state reg_lookup].
    intros; logical_simplify.
    cbv [set_out_regs]. apply map.map_ext; intros.
    rewrite !map.get_put_dec.
    repeat destruct_one_match; congruence.
  Qed.

  Lemma aes_data_get_wait_correct :
    program_logic_goal_for_function! aes_data_get_wait.
  Proof.
    (* initial processing *)
    repeat straightline.
    simplify_implicits.

    set (max_iterations:=fun s : parameters.state =>
                           match s with
                           | BUSY _ _ n => n
                           | DONE _ => 1%nat
                           | _ => 0%nat
                           end).

    (* begin while loop *)
    let l := lazymatch goal with |- cmd _ _ _ _ ?l _ => l end in
    apply atleastonce_localsmap
      with (v0:=max_iterations s)
           (lt:=lt)
           (invariant:=
              fun i tr' m' l' =>
                exists (s' : parameters.state) is_valid,
                  (* s' is the state for the new trace *)
                  execution tr' s'
                  (* the remaining maximum iterations match the "measure" i *)
                  /\ max_iterations s' = i
                  (* as long as the loop continues, we keep setting is_valid to
                     0, so locals are unchanged until the loop breaks *)
                  /\ l' = map.put l "is_valid" is_valid
                  (* expected output still matches *)
                  /\ output_matches_state out s'
                  (* s' is related to s either by decrementing counter or being equal *)
                  /\ match s with
                    | BUSY rs out n => exists n', s' = BUSY rs out n'
                    | DONE rs => s' = s
                    | _ => False
                    end
                  (* memory is unaffected *)
                  /\ (array scalar32 (word.of_Z 4) data_ptr [data0; data1; data2; data3] ⋆ R)%sep m').
    { apply lt_wf. }

    { (* case in which the loop breaks immediately (cannot happen) *)
      repeat straightline.
      exfalso. (* proof by contradiction *)

      repeat lazymatch goal with
             | v := word.of_Z 0 |- _ => subst v
             | br := if word.eqb _ (word.of_Z 0) then _ else _ |- _ => subst br
             end.
      rewrite @word.unsigned_eqb in * by typeclasses eauto.
      autorewrite with push_unsigned in *.
      destruct_one_match_hyp_of_type bool; congruence. }

    { (* proof that invariant holds at loop start *)
      do 2 eexists; ssplit;
      lazymatch goal with
      | |- execution _ _ => eassumption
      | |- (?x <= ?x)%nat => reflexivity
      | |- ?x = ?x => reflexivity
      | |- sep _ _ _ => eassumption
      | |- _ = map.put _ _ _ => symmetry; solve [apply map.put_put_same]
      | |- output_matches_state _ _ =>
        cbv [output_matches_state] in *;
        destruct_one_match; solve [eauto]
      | _ => idtac
      end; [ ].
      destruct_one_match; eauto. }

    { (* invariant holds through loop (or postcondition holds, if loop breaks) *)
      repeat straightline.

      (* Call aes_data_valid *)
      straightline_call; eauto; [ ].

      (* simplify guarantees *)
      logical_simplify; subst.
      lazymatch goal with
      | H : execution (_ :: _) _ |- _ =>
        pose proof H;
        apply invert1_execution in H; logical_simplify
      end.
      invert_step; subst.
      cbn [parameters.reg_addr parameters.write_step parameters.read_step
                               state_machine_parameters] in *.
      infer; subst.
      (* assert that the register address we just read is STATUS *)
      lazymatch goal with
      | H : reg_addr ?r = AES_STATUS |- _ =>
        apply (reg_addr_unique r STATUS) in H; subst
      end.
      invert_read_step; infer; subst; try discriminate;
        (* get rid of cases that are not BUSY or DONE *)
        try lazymatch goal with
            | H : output_matches_state _ _ |- _ =>
              cbv [output_matches_state] in H; contradiction H
            end;
        (* three cases left : BUSY -> DONE, BUSY -> BUSY, DONE -> DONE *)
        [ | | ].

      { (* case in which the state was BUSY, but is now DONE *)
        repeat straightline.
        { (* continuation case -- contradiction *)
          exfalso.
          cbv [status_matches_state] in *.
          repeat invert_bool.
          simplify_implicits.
          lazymatch goal with
          | br := if word.eqb _ (word.of_Z 0) then _ else _,
                  H : word.unsigned br <> 0 |- _ =>
                  subst br; apply H
          end.
          push_unsigned.
          destruct_one_match; subst; try reflexivity; [ ].
          (* TODO: add to invert_bool *)
          lazymatch goal with
          | H:true = negb _ |- _ => symmetry in H; apply Bool.negb_true_iff in H
          end.
          congruence. }
        { (* break case *)

          (* Call aes_data_get *)
          straightline_call; eauto using nregs_populated_set_out_regs; [ ].
          repeat straightline.
          logical_simplify; subst.
          lazymatch goal with
          | H : execution (_ :: _) _ |- _ =>
            apply invert1_execution in H; logical_simplify
          end.
          infer; subst.
          (* assert that the register address we just read is STATUS *)
          lazymatch goal with
          | H : parameters.reg_addr ?r = AES_STATUS |- _ =>
            replace AES_STATUS with (reg_addr STATUS) in H
              by (cbn [reg_addr]; subst_lets; ring);
              apply reg_addr_unique in H; try subst r
          end.
          cbn [parameters.reg_addr parameters.write_step parameters.read_step
                                   state_machine_parameters] in *.
          invert_read_step; subst; try discriminate; [ ].
          infer.

          (* postcondition *)
          lazymatch goal with
          | H : output_matches_state ?out _ |- context [?out] =>
            cbv [output_matches_state] in H; subst
          end.
          cbv [reg_lookup set_out_regs] in *.
          repeat lazymatch goal with
                 | H : map.get (map.put _ ?k _) ?k = _ |- _ => rewrite map.get_put_same in H
                 | H : map.get (map.put _ _ _) _ = _ |- _ =>
                   rewrite map.get_put_diff in H by (apply reg_addr_neq; congruence)
                 | H : context [map.remove (map.put _ ?k _) ?k] |- _ =>
                   rewrite map_remove_put_same in H
                 | H : context [map.remove (map.put _ _ _) _] |- _ =>
                   rewrite map_remove_put_diff in H by (apply reg_addr_neq; congruence)
                 | H : Some _ = Some _ |- _ => inversion H; clear H; subst
                 end.
          cbn [get_register_state].
          ssplit; eauto. } }

      { (* case in which the state was BUSY and is still BUSY *)
        repeat straightline.
        { (* continuation case *)
          cbn [max_iterations]. cbv [Markers.split].
          match goal with |- exists v, _ /\ (v < S ?n)%nat => exists n end.
          split; [ | lia ].

          (* invariant still holds *)
          do 2 eexists; ssplit;
            lazymatch goal with
            | |- execution _ _ => eassumption
            | |- max_iterations _ = _ => reflexivity
            | |- sep _ _ _ => eassumption
            | |- @eq map.rep ?l1 ?l2 =>
              subst1_map l1;
                lazymatch goal with
                | |- @eq map.rep ?l1 ?l2 =>
                  subst1_map l1
                end;
                apply map.put_put_same
            | |- exists n, ?f ?x = ?f n => exists x; reflexivity
            | |- output_matches_state _ _ =>
              cbv [output_matches_state] in *; solve [eauto]
            | _ => idtac
            end. }
        { (* break case -- contradiction *)
          exfalso.
          cbv [status_matches_state] in *.
          repeat invert_bool; try congruence; [ ].
          lazymatch goal with
          | H : word.eqb _ _ = negb (is_flag_set ?x ?flag),
                H' : is_flag_set ?x ?flag = _ |- _ =>
            rewrite H' in H; cbn [negb] in H
          end.
          simplify_implicits.
          lazymatch goal with
          | br := if word.eqb ?x (word.of_Z 0) then _ else _,
                  Heq : word.eqb ?x (word.of_Z 0) = _,
                  Hz : word.unsigned br = 0 |- _ =>
                  subst br; rewrite Heq in Hz;
                    autorewrite with push_unsigned in Hz
          end.
          discriminate. } }

      { (* case in which the state was DONE to begin with *)
        repeat straightline.
        { (* continuation case -- contradiction *)
          exfalso.
          cbv [status_matches_state] in *.
          repeat invert_bool.
          simplify_implicits.
          lazymatch goal with
          | br := if word.eqb _ (word.of_Z 0) then _ else _,
                  H : word.unsigned br <> 0 |- _ =>
                  subst br; apply H
          end.
          push_unsigned.
          destruct_one_match; subst; try reflexivity; [ ].
          (* TODO: add to invert_bool *)
          lazymatch goal with
          | H:true = negb _ |- _ => symmetry in H; apply Bool.negb_true_iff in H
          end.
          congruence. }
        { (* break case *)

          (* Call aes_data_get *)
          straightline_call; eauto;
          lazymatch goal with
          | |- nregs_populated ?rs DataOutReg = _ =>
            erewrite <-(output_matches_state_set_out_regs rs) by eassumption;
            solve [eapply nregs_populated_set_out_regs]
          | _ => idtac
          end; [ ].
          repeat straightline.
          logical_simplify; subst.
          lazymatch goal with
          | H : execution (_ :: _) _ |- _ =>
            apply invert1_execution in H; logical_simplify
          end.
          infer; subst.
          (* assert that the register address we just read is STATUS *)
          lazymatch goal with
          | H : parameters.reg_addr ?r = AES_STATUS |- _ =>
            replace AES_STATUS with (reg_addr STATUS) in H
              by (cbn [reg_addr]; subst_lets; ring);
              apply reg_addr_unique in H; try subst r
          end.
          cbn [parameters.reg_addr parameters.write_step parameters.read_step
                                   state_machine_parameters] in *.
          invert_read_step; subst; try discriminate; [ ].
          infer.

          (* postcondition *)
          lazymatch goal with
          | H : output_matches_state ?out _ |- context [?out] =>
            cbv [output_matches_state] in H; subst
          end.
          cbv [reg_lookup set_out_regs] in *. logical_simplify.
          repeat lazymatch goal with
                 | H : map.get (map.put _ ?k _) ?k = _ |- _ => rewrite map.get_put_same in H
                 | H : map.get (map.put _ _ _) _ = _ |- _ =>
                   rewrite map.get_put_diff in H by (apply reg_addr_neq; congruence)
                 | H : context [map.remove (map.put _ ?k _) ?k] |- _ =>
                   rewrite map_remove_put_same in H
                 | H : context [map.remove (map.put _ _ _) _] |- _ =>
                   rewrite map_remove_put_diff in H by (apply reg_addr_neq; congruence)
                 | H1 : map.get ?m ?k = Some _, H2 : map.get ?m ?k = Some _ |- _ =>
                   rewrite H1 in H2
                 | H : Some _ = Some _ |- _ => inversion H; clear H; subst
                 end.
          cbn [get_register_state].
          ssplit; eauto. } } }
  Qed.
End Proofs.
