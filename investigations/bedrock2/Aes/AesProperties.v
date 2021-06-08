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
  Context {consts_ok : aes_constants_ok consts}.
  Existing Instance state_machine_parameters.

  (* this duplicate of locals_ok helps when Semantics.word has been changed to
     parameters.word *)
  Local Instance localsok : @map.ok string parameters.word Semantics.locals
    := Semantics.locals_ok.

  (* Plug in the right state machine parameters; typeclass inference struggles here *)
  Local Notation execution := (execution (p:=state_machine_parameters)).

  (***** General-purpose lemmas/tactics and setup *****)

  Add Ring wring : (Properties.word.ring_theory (word := parameters.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := parameters.word)),
         constants [Properties.word_cst]).

  Existing Instance constant_literals | 10.

  (* This tactic simplifies implicit types so that they all agree; otherwise
     tactic has trouble connecting, for instance, a word of type parameters.word
     and a word of type Semantics.word, even though they are the same *)
  Local Ltac simplify_implicits :=
    change Semantics.word with parameters.word in *;
    change Semantics.mem with parameters.mem in *;
    change Semantics.width with 32 in *;
    change Semantics.word_ok with parameters.word_ok in *;
    change Semantics.mem_ok with parameters.mem_ok in *.

  (* tactic to solve the side conditions of interact_read and interact_write *)
  Local Ltac solve_dexprs ::=
    repeat straightline_with_map_lookup;
    simplify_implicits; repeat straightline_with_map_lookup.

  (* tactic to simplify side conditions in terms of [dexpr] *)
  Local Ltac dexpr_hammer :=
    subst_lets; simplify_implicits;
    repeat first [ progress push_unsigned
                 | rewrite word.unsigned_of_Z in *
                 | rewrite word.wrap_small in * by lia
                 | destruct_one_match
                 | lia
                 | progress ring_simplify
                 | reflexivity ].

  Lemma execution_unique (t : trace) s1 s2 :
    execution t s1 ->
    execution t s2 ->
    s1 = s2.
  Proof.
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
    repeat destruct_one_match_hyp; try contradiction; [ | ].
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
        | H1 : ?x = Some ?a, H2 : ?x = Some ?b |- _ =>
          rewrite H1 in H2; inversion H2; clear H2; subst
        | _ => idtac
        end.
    all:reflexivity.
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

  (* TODO: lots of annoying bit arithmetic here, maybe try to clean it up *)
  Lemma status_read_always_ok s :
    exists val s', read_step s STATUS val s'.
  Proof.
    assert (forall x y : parameters.word,
               word.slu (word.of_Z 1) x <> word.slu (word.of_Z 1) y -> x <> y)
           as Hshift_neq by (intros; subst; congruence).
    pose proof status_flags_unique_and_nonzero as Hflags.
    simplify_unique_words_in Hflags.
    repeat match goal with
           | H : _ |- _ => apply Hshift_neq in H
           end.
    pose proof status_flags_inbounds as Hbounds.
    repeat lazymatch goal with
           | H : Forall _ (_ :: _) |- _ =>
             pose proof (Forall_inv H);
               apply Forall_inv_tail in H
           | H : Forall _ [] |- _ => clear H
           end.
    cbv beta in *.
    destruct s; cbn [read_step reg_category status_matches_state].
    { exists (word.of_Z 0). eexists; ssplit; [ | reflexivity ].
      cbv [is_flag_set]. boolsimpl.
      rewrite !word.eqb_eq; [ reflexivity | apply word.unsigned_inj .. ].
      all:push_unsigned; rewrite Z.land_0_l; reflexivity. }
    { exists (word.or (word.slu (word.of_Z 1) (word.of_Z AES_STATUS_IDLE))
                 (word.slu (word.of_Z 1) (word.of_Z AES_STATUS_INPUT_READY))).
      eexists; ssplit; [ | reflexivity ].
      cbv [is_flag_set]. boolsimpl.
      repeat lazymatch goal with
             | |- (_ && _)%bool = true => apply Bool.andb_true_iff; split
             | |- negb _ = true => apply Bool.negb_true_iff
             end.
      all:rewrite word.unsigned_eqb.
      all:first [ apply Z.eqb_eq | apply Z.eqb_neq ].
      all:try lazymatch goal with
              | |- word.unsigned (word.and ?x ?y) <> _ =>
                let H := fresh in
                assert (word.unsigned (word.and x y) = word.unsigned y)
                  as H;
                  [ | rewrite H; intro Heq; apply word.unsigned_inj in Heq;
                      simplify_implicits; cbn in *; congruence ]
              end.
      all:push_unsigned; cbv [word.wrap]; rewrite <-!Z.land_ones by lia;
        bitblast.Z.bitblast.
      all:rewrite !Z_testbit_1_l;
        repeat lazymatch goal with
               | |- context [?x =? ?y] =>
                 destr (x =? y)
               end.
      all:boolsimpl; try reflexivity.
      all:subst.
      all:lazymatch goal with
          | H1 : ?i - ?x = 0,
            H2 : ?i - ?y = 0 |- _ =>
            assert (word.of_Z x = word.of_Z y) by (f_equal; lia)
          end.
      all:simplify_implicits; cbn in *; congruence. }
    { exists (word.slu (word.of_Z 1) (word.of_Z AES_STATUS_OUTPUT_VALID)).
      destruct data. rewrite is_flag_set_shift by (cbv [boolean]; tauto || lia).
      rewrite word.eqb_ne by
          (intro Heq; apply word.of_Z_inj_small in Heq; lia).
      cbn [negb]. eauto. }
    { exists (word.slu (word.of_Z 1) (word.of_Z AES_STATUS_OUTPUT_VALID)).
      eexists; split; [ | reflexivity ].
      rewrite is_flag_set_shift by (cbv [boolean]; tauto || lia).
      rewrite word.eqb_ne by
          (intro Heq; apply word.of_Z_inj_small in Heq; lia).
      rewrite !is_flag_set_shift_neq by
          (cbv [boolean];
           first [ tauto | lia
                   | intro; cbn in *; simplify_implicits; congruence ]).
      reflexivity. }
  Qed.

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
      repeat destruct_one_match;
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
        (post : trace -> mem -> locals -> Prop) rs (addr val: Semantics.word) :
    dexprs m l [addre; vale] [addr; val] ->
    addr = word.add (word.of_Z AES_KEY0) (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4)) ->
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
    addr = word.add (word.of_Z AES_IV0) (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4)) ->
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

  Definition data_in_from_index (i : nat) : Register :=
    nth i [DATA_IN0;DATA_IN1;DATA_IN2;DATA_IN3] CTRL.

  Lemma data_in_from_index_category i :
    (i < 4)%nat -> reg_category (data_in_from_index i) = DataInReg.
  Proof.
    intros. cbv [data_in_from_index].
    apply Forall_nth; [ | length_hammer ].
    repeat constructor.
  Qed.

  Lemma interact_write_data_in i call addre vale t m l
        (post : trace -> mem -> locals -> Prop) rs addr val :
    dexprs m l [addre; vale] [addr; val] ->
    addr = word.add (word.of_Z AES_DATA_IN0) (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4)) ->
    (i < 4)%nat ->
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
      exists (IDLE rs). destruct_one_match; eexists; ssplit; eauto. }
  Qed.


  Definition data_out_from_index (i : nat) : Register :=
    nth i [DATA_OUT0;DATA_OUT1;DATA_OUT2;DATA_OUT3] CTRL.

  Lemma data_out_from_index_category i :
    (i < 4)%nat -> reg_category (data_out_from_index i) = DataOutReg.
  Proof.
    intros. cbv [data_out_from_index].
    apply Forall_nth; [ | length_hammer ].
    repeat constructor.
  Qed.

  Lemma interact_read_data_out i call addre bind (t : trace) m l
        (post : trace -> mem -> locals -> Prop) data addr val :
    dexprs m l [addre] [addr] ->
    addr = word.add (word.of_Z AES_DATA_OUT0) (word.mul (word.of_Z (Z.of_nat i)) (word.of_Z 4)) ->
    (i < 4)%nat ->
    match data_out_from_index i with
    | DATA_OUT0 => done_data_out0 data
    | DATA_OUT1 => done_data_out1 data
    | DATA_OUT2 => done_data_out2 data
    | DATA_OUT3 => done_data_out3 data
    | _ => None
    end = Some val ->
    execution t (DONE data) ->
    (forall s' val,
        read_step (DONE data) (data_out_from_index i) val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, READ, [addr], (map.empty, [val])) :: t) s' ->
        post ((map.empty, READ, [addr], (map.empty, [val])) :: t)
             m (map.put l bind val)) ->
    cmd call (cmd.interact [bind] READ [addre]) t m l post.
  Proof.
    intros; eapply interact_read with (r:=data_out_from_index i);
      intros; infer;
        cbv [parameters.read_step state_machine_parameters] in *;
        eauto.
    { repeat (destruct i; try lia); subst; cbn; ring. }
    { cbv [read_step]. rewrite data_out_from_index_category by lia.
      exists (DONE data). repeat (destruct i; try lia); subst.
      all:cbn [data_out_from_index nth read_output_reg] in *.
      all:match goal with H : _ = Some _ |- _ => rewrite H end.
      all:do 2 eexists; ssplit; eauto. }
  Qed.

  Lemma get_aes_input_none data :
    (idle_data_in0 data = None
     \/ idle_data_in1 data = None
     \/ idle_data_in2 data = None
     \/ idle_data_in3 data = None) ->
    get_aes_input data = None.
  Proof.
    cbv [get_aes_input]. destruct data; cbn; intros.
    repeat lazymatch goal with
           | H : _ \/ _ |- _ => destruct H
           | H : ?x = None |- _ => rewrite H
           end.
    all:repeat destruct_one_match; reflexivity.
  Qed.

  (* apply interact_read_status and do some post-processing *)
  Local Ltac read_status :=
    eapply interact_read_status; [ try post_interaction .. | ].

  (* apply interact_write_status and do some post-processing *)
  Local Ltac write_control :=
    eapply interact_write_control; [ try post_interaction .. | ].

  (* apply interact_write_key and do some post-processing *)
  Local Ltac write_key :=
    eapply interact_write_key;
    [ try post_interaction ..
    | intros;
      try lazymatch goal with
          | H : write_step _ _ _ _ |- _ =>
            cbv [write_step] in H;
            rewrite key_from_index_category in H by lia; subst
          end ].

  (* apply interact_write_iv for the nth IV register, and do some
     post-processing *)
  Local Ltac write_iv_n n :=
    eapply interact_write_iv with (i:=n);
    [ try post_interaction ..
    | intros;
      try lazymatch goal with
          | H : write_step _ _ _ _ |- _ =>
            cbv [write_step] in H;
            rewrite iv_from_index_category in H by lia; subst
          end ].

  (* apply interact_write_data_in for the nth DATA_IN register, and do some
     post-processing *)
  Local Ltac write_data_in_n n :=
    eapply interact_write_data_in with (i:=n);
    [ lazymatch goal with
      | |- _ = word.add _ _ =>
        subst_lets; simplify_implicits;
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; ring
      | _ => idtac
      end;
      try post_interaction ..
    | intros;
      try lazymatch goal with
          | H : write_step _ _ _ _ |- _ =>
            cbv [write_step] in H;
            rewrite data_in_from_index_category in H by lia; subst
          end
    ].

  (* same as write_data_in_n but with extra processing to prove we didn't
     transition to the BUSY state after the write because there are still
     unwritten input registers *)
  Local Ltac write_data_in_nonlast_n n :=
    write_data_in_n n;
    [ ..
    | lazymatch goal with
      | H : context [match get_aes_input ?d with _ => _ end] |- _ =>
        cbn [data_in_from_index nth] in H;
        rewrite get_aes_input_none in H
          by (cbv [write_input_reg];
              repeat match goal with H : ?x = None |- _ => rewrite H end;
              tauto)
      end
    ].

  (* apply interact_read_data_out for the nth DATA_OUT register, and do some
     post-processing *)
  Local Ltac read_data_out_n n :=
    eapply interact_read_data_out with (i:=n);
    [lazymatch goal with
      | |- _ = word.add _ _ =>
        subst_lets; simplify_implicits;
        cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; ring
      | _ => idtac
      end;
      try post_interaction ..
    | intros;
      try lazymatch goal with
          | H : read_step _ _ _ _ |- _ =>
            cbv [read_step] in H;
            rewrite data_out_from_index_category in H by lia;
            cbn [read_step read_output_reg data_out_from_index nth] in H;
            cbn [done_data_out0 done_data_out1 done_data_out2 done_data_out3] in H;
            destruct H as [? [H ?]];
            inversion H; clear H; subst
          end
    ];
    (* try eauto on leftover side condtions now that evars have been filled
       in *)
    [
      cbn [data_out_from_index nth done_data_out0 done_data_out1
                               done_data_out2 done_data_out3];
      eauto .. | ].

  Local Notation aes_op_t := (enum_member aes_op) (only parsing).
  Local Notation aes_mode_t := (enum_member aes_mode) (only parsing).
  Local Notation aes_key_len_t := (enum_member aes_key_len) (only parsing).

  Definition ctrl_operation (ctrl : parameters.word) : bool :=
    is_flag_set ctrl AES_CTRL_OPERATION.
  Definition ctrl_mode (ctrl : parameters.word) : parameters.word :=
    select_bits ctrl (word.of_Z AES_CTRL_MODE_OFFSET) (word.of_Z AES_CTRL_MODE_MASK).
  Definition ctrl_key_len (ctrl : parameters.word) : parameters.word :=
    select_bits ctrl (word.of_Z AES_CTRL_KEY_LEN_OFFSET) (word.of_Z AES_CTRL_KEY_LEN_MASK).
  Definition ctrl_manual_operation (ctrl : parameters.word) : bool :=
    is_flag_set ctrl AES_CTRL_MANUAL_OPERATION.

  (***** Proofs for specific functions *****)

  Global Instance spec_of_aes_data_ready : spec_of aes_data_ready :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) (s : state),
        (* no special requirements of the memory *)
        R m ->
        (* no constraints on current state *)
        execution tr s ->
        call function_env aes_data_ready tr m []
             (fun tr' m' rets =>
                exists (status out : Semantics.word) (s' : state),
                  (* the new state matches the new trace *)
                  execution tr' s'
                  (* ...and there exists a single valid status-read step between
                     the old and new state, and the read result was [status] *)
                  /\ read_step s STATUS status s'
                  (* ...and all the same properties as before hold on the memory *)
                  /\ R m'
                  (* ...and there is one output value *)
                  /\ rets = [out]
                  (* ...and the output value is zero if and only if the
                     input_ready flag is unset *)
                  /\ word.eqb out (word.of_Z 0)
                    = negb (is_flag_set status AES_STATUS_INPUT_READY)).

(* BEGIN TODO integrate into bedrock2.ProgramLogic *)

Ltac bind_body_of_function f_ ::=
  let f := Tactics.rdelta.rdelta f_ in
  let fname := open_constr:(_) in
  let fargs := open_constr:(_) in
  let frets := open_constr:(_) in
  let fbody := open_constr:(_) in
  let funif := open_constr:((fname, (fargs, frets, fbody))) in
  unify f funif;
  let G := lazymatch goal with |- ?G => G end in
  let P := lazymatch eval pattern f_ in G with ?P _ => P end in
  change (bindcmd fbody (fun c : Syntax.cmd => P (fname, (fargs, frets, c))));
  cbv beta iota delta [bindcmd]; intros.

Ltac app_head e :=
  match e with
  | ?f ?a => app_head f
  | _ => e
  end.

(* note: f might have some implicit parameters (eg a record of constants) *)
Ltac enter f ::=
  let fname := app_head f in
  cbv beta delta [program_logic_goal_for]; intros;
  bind_body_of_function f;
  let fdefn := eval cbv delta [fname] in f in
  let ctx := string2ident.learn fdefn in
  let H := fresh "_string_to_ident" in
  pose ctx as H;
  lazymatch goal with |- ?s _ => cbv beta delta [s] end.

(* END TODO *)

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
        call function_env aes_data_valid tr m []
             (fun tr' m' rets =>
                exists (status out : Semantics.word) (s' : state),
                  (* the new state matches the new trace *)
                  execution tr' s'
                  (* ...and there exists a single valid status-read step between
                     the old and new state, and the read result was [status] *)
                  /\ read_step s STATUS status s'
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
        call function_env aes_idle tr m []
             (fun tr' m' rets =>
                exists (status out : Semantics.word) (s' : state),
                  (* the new state matches the new trace *)
                  execution tr' s'
                  (* ...and there exists a single valid status-read step between
                     the old and new state, and the read result was [status] *)
                  /\ read_step s STATUS status s'
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
        call function_env aes_init tr m args
             (fun tr' m' rets =>
                (* the circuit is in IDLE state with the correct control
                   register value and no other known register values *)
                (exists ctrl,
                    execution tr' (IDLE (Build_idle_data ctrl None None None None
                                                           None None None None
                                                           None None None None
                                                           None None None None))
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

    write_control; [ cbn iota; trivial | ].
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

    assert (0 <= AES_CTRL_MODE_MASK < 2 ^ 32). {
      rewrite mode_mask_eq.
      rewrite Z.ones_equiv.
      pose proof Z.pow_lt_mono_r 2 mode_size 32.
      pose proof Z.pow_pos_nonneg 2 mode_size.
      cbn in *. lia.
    }
    assert (0 <= AES_CTRL_KEY_LEN_MASK < 2 ^ 32). {
      rewrite key_len_mask_eq.
      rewrite Z.ones_equiv.
      pose proof Z.pow_lt_mono_r 2 key_len_size 32.
      pose proof Z.pow_pos_nonneg 2 key_len_size.
      cbn in *. lia.
    }

    (* split cases *)
    eexists; ssplit.
    { (* prove that the execution trace is OK *)
      subst; eassumption. }
    { (* prove that the "operation" flag is correct *)
      cbv [ctrl_operation].
      rewrite !is_flag_set_or_shiftl_low by lia.
      apply is_flag_set_shift; eauto using size1_boolean.
      lia. }
    (* TODO automate in a *robust* way... *)
    { cbv [ctrl_mode].
      etransitivity. {
        eapply select_bits_or_shiftl_low.
        all: rewrite ?word.unsigned_of_Z_nowrap.
        1: eassumption.
        all: try lia.
      }
      etransitivity. {
        eapply select_bits_or_shiftl_low.
        all: rewrite ?word.unsigned_of_Z_nowrap.
        1: eassumption.
        all: try lia.
      }
      etransitivity. {
        rewrite mode_mask_eq in *.
        eapply select_bits_or_shiftl_high.
        all: rewrite ?word.unsigned_of_Z_nowrap.
        3: {
          eapply has_size_ones.
          rewrite word.unsigned_of_Z_nowrap; trivial.
        }
        all: try (cbn in *; lia).
        eapply has_size_weaken.
        1: eapply has_size_slu.
        1: eassumption.
        all: rewrite ?word.unsigned_of_Z_nowrap.
        all: try (cbn -[Z.add] in *; lia).
      }
      etransitivity. {
        eapply select_bits_id.
        1: eassumption.
        all: rewrite ?word.unsigned_of_Z_nowrap.
        all: try (cbn in *; lia).
      }
      reflexivity.
    }
    { cbv [ctrl_key_len].
      etransitivity. {
        eapply select_bits_or_shiftl_low.
        all: rewrite ?word.unsigned_of_Z_nowrap.
        1: eassumption.
        all: try lia.
      }
      etransitivity. {
        rewrite key_len_mask_eq in *.
        eapply select_bits_or_shiftl_high.
        all: rewrite ?word.unsigned_of_Z_nowrap.
        3: {
          eapply has_size_ones.
          rewrite word.unsigned_of_Z_nowrap; trivial.
        }
        all: try (cbn in *; lia).
        eapply has_size_weaken.
        { eapply has_size_or.
          { eapply has_size_slu. 1: eassumption.
            rewrite word.unsigned_of_Z_nowrap.
            all: try (cbn -[Z.add] in *; lia). }
          { eapply has_size_slu.
            { eapply has_size_and. 1: eassumption.
              rewrite mode_mask_eq. eapply has_size_ones.
              rewrite word.unsigned_of_Z_nowrap. 1: reflexivity.
              cbn in *; lia.
              all: try (cbn -[Z.add] in *; lia). }
            rewrite word.unsigned_of_Z_nowrap; lia. }
        }
        rewrite ?word.unsigned_of_Z_nowrap.
        all: cbn -[Z.add] in *; try lia.
      }
      eapply select_bits_id.
      1: eassumption.
      all: rewrite ?word.unsigned_of_Z_nowrap.
      all: try (cbn in *; lia).
    }
    { cbv [ctrl_manual_operation].
      apply is_flag_set_or_shiftl_high.
      1: eassumption.
      1: cbn in *; lia.
      eapply has_size_weaken.
      { eapply has_size_or.
        { eapply has_size_or.
          { eapply has_size_slu. 1: eassumption.
            rewrite word.unsigned_of_Z_nowrap.
            all: try (cbn -[Z.add] in *; lia). }
          { eapply has_size_slu.
            { eapply has_size_and. 1: eassumption.
              rewrite mode_mask_eq. eapply has_size_ones.
              rewrite word.unsigned_of_Z_nowrap. 1: reflexivity.
              cbn in *; lia.
              all: try (cbn -[Z.add] in *; lia). }
            rewrite word.unsigned_of_Z_nowrap; lia. }
        }
        eapply has_size_slu.
        { eapply has_size_and. 1: eassumption. rewrite key_len_mask_eq.
          eapply has_size_ones.
          rewrite ?word.unsigned_of_Z_nowrap. 1: reflexivity.
          all: cbn -[Z.add] in *; try lia.
        }
        rewrite ?word.unsigned_of_Z_nowrap.
        all: try (cbn in *; lia).
      }
      rewrite ?word.unsigned_of_Z_nowrap.
      all: cbn -[Z.add] in *; try lia.
    }
  Qed.

  Global Instance spec_of_aes_key_put : spec_of aes_key_put :=
    fun function_env =>
      forall (tr : trace) (m : mem) R (data : idle_data)
        (key_len key_arr_ptr : Semantics.word) (key_arr : list Semantics.word),
        (* key_len is a member of the aes_key_len enum *)
        aes_key_len_t key_len ->
        (* key array is in memory *)
        (array scalar32 (word.of_Z 4) key_arr_ptr key_arr * R)%sep m ->
        (* key array length matches the key_len argument *)
         length key_arr = (if word.eqb key_len (word.of_Z kAes128)
                           then 4%nat else if word.eqb key_len (word.of_Z kAes192)
                                       then 6%nat else 8%nat) ->
        (* circuit must be in IDLE state *)
        execution tr (IDLE data) ->
        let args := [key_arr_ptr; key_len] in
        call function_env aes_key_put tr m args
             (fun tr' m' rets =>
                (* the circuit is in IDLE state with the key registers updated *)
                execution tr'
                          (IDLE (fold_left
                                   (fun data i =>
                                      write_input_reg (key_from_index i) data (nth i key_arr (word.of_Z 0)))
                                   (seq 0 8) data))
                (* ...and the same properties as before hold on the memory *)
                /\ (array scalar32 (word.of_Z 4) key_arr_ptr key_arr * R)%sep m'
                (* ...and there is no output *)
                /\ rets = []).

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
    move H at bottom.
    lazymatch goal with
    | H : enum_member aes_key_len ?len |- _ =>
      cbn in H
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
      all:repeat (destruct_one_match_hyp_of_type bool;
                  (* TODO don't use cbn so aggressively *)
                  cbn -[map.put map.empty] in *; try congruence);
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
                execution
                  tr'
                  (IDLE
                     (fold_left
                        (fun data i =>
                           write_input_reg
                             (key_from_index i) data
                             (nth i key_arr (word.of_Z 0)))
                        (seq 0 (length key_arr - v))
                        data))
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
      cbn [firstn fold_left]. eassumption. }

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
        | l := map.put _ "i" ?i,
               H : word.unsigned ?i < _ |- _ =>
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
        autorewrite with pull_snoc natsimpl.
        rewrite <-!hd_skipn.
        eassumption. }

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
             execution
               tr'
               (IDLE
                  (fold_left
                     (fun data i =>
                        write_input_reg
                          (key_from_index i) data
                          (nth i key_arr (word.of_Z 0)))
                     (seq 0 (8 - v))
                     data))
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
          (*
          rewrite Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.*)
          ssplit;
          lazymatch goal with
            | |- ?m = map.put ?m _ _ =>
              subst1_map m; rewrite map.put_put_same; reflexivity
            | |- sep _ _ _ => ecancel_assumption
            | |- (_ < _)%nat => lia
            | |- (_ <= _)%nat => lia
            | _ => idtac
          end.

          lazymatch goal with
          | H : context [write_input_reg _ (fold_left _ (seq 0 ?n) _)]
            |- context [fold_left _ (seq 0 ?m)] =>
            replace (seq 0 m) with (seq 0 (S n)) by (f_equal; lia)
          end.
          autorewrite with pull_snoc natsimpl.
          rewrite <-!hd_skipn.
          eassumption. }

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

          (* list simplifications *)
          autorewrite with pull_snoc natsimpl.
          autorewrite with push_nth.

          (* solve *)
          eassumption. }

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

            lazymatch goal with
            | H : context [fold_left _ (seq 0 (8 - ?v))] |- _ =>
              replace (8 - v)%nat with 8%nat in H by lia
            end.
            eassumption. } } } }
  Qed.

  Global Instance spec_of_aes_iv_put : spec_of aes_iv_put :=
    fun function_env =>
      forall (tr : trace) (m : mem) R (data : idle_data)
        (iv_ptr : Semantics.word) (iv_arr : list Semantics.word),
        (* iv array is in memory *)
        (array scalar32 (word.of_Z 4) iv_ptr iv_arr * R)%sep m ->
        (* iv array has 4 elements *)
        length iv_arr = 4%nat ->
        (* circuit must be in IDLE state *)
        execution tr (IDLE data) ->
        call function_env aes_iv_put tr m [iv_ptr]
             (fun tr' m' rets =>
                (* the circuit is in IDLE state with the iv registers updated *)
                execution tr'
                          (IDLE (fold_left
                                   (fun data i =>
                                      write_input_reg (iv_from_index i) data
                                                      (nth i iv_arr (word.of_Z 0)))
                                   (seq 0 4) data))
                (* ...and the same properties as before hold on the memory *)
                /\ (array scalar32 (word.of_Z 4) iv_ptr iv_arr * R)%sep m'
                (* ...and there is no output *)
                /\ rets = []).

  Lemma aes_iv_put_correct :
    program_logic_goal_for_function! aes_iv_put.
  Proof.
    (* intial processing *)
    repeat straightline.
    simplify_implicits.

    (* simplify array predicate *)
    destruct_lists_by_length.
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
      forall (tr : trace) (m : mem) R (data : idle_data) all_aes_input
        (input_ptr : Semantics.word) (input_arr : list Semantics.word),
        (* input array is in memory *)
        (array scalar32 (word.of_Z 4) input_ptr input_arr * R)%sep m ->
        (* input array has 4 elements *)
        length input_arr = 4%nat ->
        (* circuit must be in IDLE state *)
        execution tr (IDLE data) ->
        (* input-data registers must not be currently set *)
        data.(idle_data_in0) = None ->
        data.(idle_data_in1) = None ->
        data.(idle_data_in2) = None ->
        data.(idle_data_in3) = None ->
        (* adding input-data registers must result in a full set of data
           (i.e. key and iv registers are already set) *)
        get_aes_input
          (fold_left
             (fun data i =>
                write_input_reg (data_in_from_index i) data
                                (nth i input_arr (word.of_Z 0)))
             (seq 0 4) data) = Some all_aes_input ->
        call function_env aes_data_put tr m [input_ptr]
             (fun tr' m' rets =>
                (* the circuit is now in the BUSY state *)
                execution tr' (BUSY (Build_busy_data
                                       (idle_ctrl data)
                                       (aes_expected_output all_aes_input)
                                       timing.ndelays_core))
                (* ...and the same properties as before hold on the memory *)
                /\ (array scalar32 (word.of_Z 4) input_ptr input_arr * R)%sep m'
                (* ...and there is no output *)
                /\ rets = []).

  Lemma aes_data_put_correct :
    program_logic_goal_for_function! aes_data_put.
  Proof.
    (* initial processing *)
    repeat straightline.
    simplify_implicits.

    (* simplify array predicate *)
    destruct_lists_by_length.
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
    write_data_in_nonlast_n 0%nat. repeat straightline.

    (* i = 1 *)
    split; repeat straightline; [ dexpr_hammer | ].
    write_data_in_nonlast_n 1%nat. repeat straightline.

    (* i = 2 *)
    split; repeat straightline; [ dexpr_hammer | ].
    write_data_in_nonlast_n 2%nat. repeat straightline.

    (* i = 3 *)
    split; repeat straightline; [ dexpr_hammer | ].
    write_data_in_n 3%nat. repeat straightline.
    lazymatch goal with
    | H1 : get_aes_input (fold_left _ _ _) = Some _,
      H2 : context [match get_aes_input _ with _ => _ end] |- _ =>
      cbn [fold_left seq nth data_in_from_index] in H1, H2;
        rewrite H1 in H2
    end.

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

  (* TODO: the real state machine is slightly more complex; AES block can get
     input while BUSY and stalls in BUSY state until output is read. The spec
     should be modified to account for this behavior. For now, this spec is
     exactly the same as aes_data_put. *)
  Global Instance spec_of_aes_data_put_wait : spec_of aes_data_put_wait :=
    fun function_env =>
      forall (tr : trace) (m : mem) R (data : idle_data) all_aes_input
        (input_ptr : Semantics.word) (input_arr : list Semantics.word),
        (* input array is in memory *)
        (array scalar32 (word.of_Z 4) input_ptr input_arr * R)%sep m ->
        (* input array has 4 elements *)
        length input_arr = 4%nat ->
        (* circuit must be in IDLE state *)
        execution tr (IDLE data) ->
        (* input-data registers must not be currently set *)
        data.(idle_data_in0) = None ->
        data.(idle_data_in1) = None ->
        data.(idle_data_in2) = None ->
        data.(idle_data_in3) = None ->
        (* adding input-data registers must result in a full set of data
           (i.e. key and iv registers are already set) *)
        get_aes_input
          (fold_left
             (fun data i =>
                write_input_reg (data_in_from_index i) data
                                (nth i input_arr (word.of_Z 0)))
             (seq 0 4) data) = Some all_aes_input ->
        call function_env aes_data_put_wait tr m [input_ptr]
             (fun tr' m' rets =>
                (* the circuit is now in the BUSY state *)
                execution tr' (BUSY (Build_busy_data
                                       (idle_ctrl data)
                                       (aes_expected_output all_aes_input)
                                       timing.ndelays_core))
                (* ...and the same properties as before hold on the memory *)
                /\ (array scalar32 (word.of_Z 4) input_ptr input_arr * R)%sep m'
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
    cbn [read_step reg_category] in *.
    cbv [status_matches_state] in *.
    logical_simplify; simplify_implicits.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H; destruct H
           | H : word.eqb _ _ = _ |- _ => apply word.eqb_false in H
           | H : is_flag_set _ _  = _ |- _ => progress rewrite H in *
           end.
    subst.

    (* loop done *)
    repeat straightline.
    split; repeat straightline; [ dexpr_hammer; congruence | ].

    (* call aes_data_put *)
    straightline_call; eauto; [ ].

    (* simplify guarantees *)
    logical_simplify; subst.

    (* done; prove postcondition *)
    repeat straightline. eauto.
  Qed.

  Global Instance spec_of_aes_data_get : spec_of aes_data_get :=
    fun function_env =>
      forall (tr : trace) (m : mem) R (data : done_data)
        (data_ptr out0 out1 out2 out3 : Semantics.word)
        (data_arr : list Semantics.word),
        (* data array is in memory, with arbitrary initital values *)
        (array scalar32 (word.of_Z 4) data_ptr data_arr * R)%sep m ->
        length data_arr = 4%nat ->
        (* circuit must be in the DONE state *)
        execution tr (DONE data) ->
        (* the output registers must all be populated *)
        data.(done_data_out0) = Some out0 ->
        data.(done_data_out1) = Some out1 ->
        data.(done_data_out2) = Some out2 ->
        data.(done_data_out3) = Some out3 ->
        call function_env aes_data_get tr m [data_ptr]
             (fun tr' m' rets =>
                (* the circuit is now in the IDLE state with output registers unset *)
                execution tr' (IDLE (Build_idle_data
                                       (done_ctrl data) None None None None None None None None
                                       None None None None None None None None))
                (* ...and the array now holds the values from the output registers *)
                /\ (array scalar32 (word.of_Z 4) data_ptr [out0;out1;out2;out3] * R)%sep m'
                (* ...and there are no return values *)
                /\ rets = []).


  Lemma aes_data_get_correct :
    program_logic_goal_for_function! aes_data_get.
  Proof.
    (* initial processing *)
    repeat straightline.
    simplify_implicits.

    (* simplify array predicate *)
    destruct_lists_by_length.
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

    destruct data;
      cbn [AesSemantics.done_ctrl
             AesSemantics.done_data_out0
             AesSemantics.done_data_out1
             AesSemantics.done_data_out2
             AesSemantics.done_data_out3] in *; subst.

    (* i = 0 *)
    split; repeat straightline; [ dexpr_hammer | ].

    (* read register *)
    read_data_out_n 0%nat. repeat straightline.

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
    read_data_out_n 1%nat. repeat straightline.

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
    read_data_out_n 2%nat. repeat straightline.

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
    read_data_out_n 3%nat. repeat straightline.

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

    ssplit; eauto; [ ].
    simplify_implicits.
    ecancel_assumption.
  Qed.

  Definition output_matches_state (out : aes_output) (s : state) : Prop :=
    match s with
    | BUSY data => busy_exp_output data = out
    | DONE data =>
      data = done_data_from_output (done_ctrl data) out
    | _ => False
    end.

  Definition get_ctrl (s : state) : Semantics.word :=
    match s with
    | UNINITIALIZED => word.of_Z 0 (* dummy value *)
    | IDLE data => idle_ctrl data
    | BUSY data => busy_ctrl data
    | DONE data => done_ctrl data
    end.

  Global Instance spec_of_aes_data_get_wait : spec_of aes_data_get_wait :=
    fun function_env =>
      forall (tr : trace) (m : mem) R (out : aes_output)
        (data_ptr : Semantics.word) (data_arr : list Semantics.word) (s : state),
        (* data array is in memory, with arbitrary initital values *)
        (array scalar32 (word.of_Z 4) data_ptr data_arr * R)%sep m ->
        length data_arr = 4%nat ->
        (* circuit must be in the DONE or BUSY state (otherwise we can't prove
           termination) and expected or already-written output matches out *)
        execution tr s ->
        output_matches_state out s ->
        call function_env aes_data_get_wait tr m [data_ptr]
             (fun tr' m' rets =>
                (* the circuit is now in the IDLE state with output registers unset *)
                execution tr' (IDLE (Build_idle_data (get_ctrl s) None None None None
                                                     None None None None None None None None
                                                     None None None None))
                (* ...and the array now holds the values from the expected output *)
                /\ (array scalar32 (word.of_Z 4) data_ptr
                         [out.(data_out0)
                          ; out.(data_out1)
                          ; out.(data_out2)
                          ; out.(data_out3)] * R)%sep m'
                (* ...and there are no return values *)
                /\ rets = []).

  Lemma aes_data_get_wait_correct :
    program_logic_goal_for_function! aes_data_get_wait.
  Proof.
    (* initial processing *)
    repeat straightline.
    simplify_implicits.

    (* separate out cases where s is initially BUSY or DONE *)
    cbv [output_matches_state] in *.
    destruct s; try contradiction; [ | ].

    { (* case in which the initial state is BUSY *)
      lazymatch goal with
        H : execution tr (BUSY data) |- _ =>
        destruct data as [ctrl exp_output max_cycles];
          cbn [get_ctrl] in *;
          cbn [busy_ctrl busy_exp_output busy_max_cycles_until_done] in *
      end.
      subst.

      (* begin while loop *)
      let l := lazymatch goal with |- cmd _ _ _ _ ?l _ => l end in
      apply atleastonce_localsmap
        with (v0:=max_cycles)
             (lt:=lt)
             (invariant:=
                fun i tr' m' l' =>
                  exists (s' : state) is_valid,
                    (* s' is the state for the new trace *)
                    execution tr' s'
                    (* as long as the loop continues, we keep setting is_valid to
                       0, so locals are unchanged until the loop breaks *)
                    /\ l' = map.put l "is_valid" is_valid
                    /\ (exists n',
                          (* current state has the same control and expected
                             output as the initial state, but a possibly different
                             counter *)
                          s' = BUSY (Build_busy_data ctrl out n')
                          (* the counter matches the "measure" i *)
                          /\ n' = i)
                    (* memory is unaffected *)
                    /\ (array scalar32 (word.of_Z 4) data_ptr data_arr ⋆ R)%sep m').
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
        eauto. }

      { (* invariant holds through loop (or postcondition holds, if loop breaks) *)
        intros; logical_simplify; subst.
        repeat straightline.

        (* Call aes_data_valid *)
        straightline_call; eauto; [ ].

        (* simplify guarantees *)
        logical_simplify; subst.
        cbn [read_step reg_category] in *.
        destruct_one_match_hyp.

        { (* case in which the status is now DONE; break *)
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
            straightline_call; eauto; try reflexivity; [ ].

            (* simplify guarantees *)
            logical_simplify; subst.

            (* postcondition *)
            repeat straightline.
            ssplit; eauto. } }

        { (* case in which the state is still BUSY *)
          intros; logical_simplify.
          destruct_one_match_hyp; [ contradiction | subst ].
          repeat straightline.

          { (* continuation case *)
            cbv [Markers.split].
            match goal with |- exists v, _ /\ (v < S ?n)%nat => exists n end.
            split; [ | lia ].

            (* invariant still holds *)
            do 2 eexists; ssplit;
              lazymatch goal with
              | |- execution _ _ => eassumption
              | |- sep _ _ _ => eassumption
              | |- @eq map.rep ?l1 ?l2 =>
                subst1_map l1;
                  lazymatch goal with
                  | |- @eq map.rep ?l1 ?l2 =>
                    subst1_map l1
                  end;
                  apply map.put_put_same
              | _ => eauto
              end. }
          { (* break case -- contradiction *)
            exfalso.
            cbv [status_matches_state] in *.
            repeat invert_bool; try congruence; [ ].
            simplify_implicits.
            lazymatch goal with
            | H : word.eqb _ _ = negb (is_flag_set ?x ?flag),
                  H' : is_flag_set ?x ?flag = _ |- _ =>
              rewrite H' in H; cbn [negb] in H
            end.
            lazymatch goal with
            | br := if word.eqb ?x (word.of_Z 0) then _ else _,
                    Heq : word.eqb ?x (word.of_Z 0) = _,
                          Hz : word.unsigned br = 0 |- _ =>
                    subst br; rewrite Heq in Hz;
                      autorewrite with push_unsigned in Hz
            end.
            discriminate. } } } }

    { (* case in which the initial state is DONE *)

      (* use output_matches_state precondition *)
      lazymatch goal with
      | H : ?data = done_data_from_output (done_ctrl ?data) out |- _ =>
        cbv [done_data_from_output] in H; destruct data;
        cbn [AesSemantics.done_ctrl
               AesSemantics.done_data_out0
               AesSemantics.done_data_out1
               AesSemantics.done_data_out2
               AesSemantics.done_data_out3] in *;
        inversion H; clear H; subst
      end.

      (* while loop will run exactly once *)
      eapply unroll_while with (iterations:=1%nat). cbn [repeat_logic_step].
      repeat straightline.

      (* prove that we do enter the while loop *)
      ssplit;
        [ subst_lets; rewrite word.eqb_eq by reflexivity;
          push_unsigned; congruence | ].

      repeat straightline.

      (* Call aes_data_valid *)
      straightline_call; eauto; [ ].

      (* simplify guarantees *)
      logical_simplify; subst.
      cbn [read_step reg_category] in *.
      cbv [status_matches_state] in *.
      logical_simplify; subst.
      repeat invert_bool; try congruence; [ ].
      simplify_implicits.
      lazymatch goal with
      | H : word.eqb _ _ = negb (is_flag_set ?x ?flag),
            H' : is_flag_set ?x ?flag = _ |- _ =>
        rewrite H' in H; cbn [negb] in H;
          apply word.eqb_false in H
      end.

      repeat straightline.

      (* prove the loop breaks *)
      ssplit;
        [ subst_lets; simplify_implicits;
          destruct_one_match; push_unsigned; congruence | ].

      repeat straightline.

      (* Call aes_data_get *)
      straightline_call; eauto; try reflexivity; [ ].

      (* simplify guarantees *)
      logical_simplify; subst.

      (* postcondition *)
      repeat straightline.
      ssplit; eauto. }
  Qed.
End Proofs.
