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
Require Import Bedrock2Experiments.Aes.AesSemantics.
Require Import Bedrock2Experiments.Aes.Aes.
Import Syntax.Coercions List.ListNotations.
Local Open Scope Z_scope.

Section Proofs.
  Import constants.
  Context {p : parameters} {p_ok : parameters.ok p}
          {consts : constants Z} {timing : timing}.
  Existing Instances semantics_parameters AesSemantics.ok constant_words.
  Context {consts_ok : constants.ok constant_words}.

  (***** General-purpose lemmas/tactics and setup *****)

  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).

  Existing Instance constants.constant_names | 10.

  Lemma interact_mmio call action binds arges t m l (post : trace -> mem -> locals -> Prop) args :
    dexprs m l arges args ->
    (forall s s' rets,
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

  Local Ltac subst1_map m :=
    match m with
    | map.put ?m _ _ => subst1_map m
    | ?m => is_var m; subst m
    end.

  Local Ltac map_lookup :=
    repeat lazymatch goal with
           | |- context [map.get ?l] =>
             try apply map.get_put_same; try eassumption;
             subst1_map l;
             rewrite ?map.get_put_diff by congruence
           end.

  Local Ltac straightline_with_map_lookup :=
    lazymatch goal with
    | |- exists v, map.get _ _ = Some v /\ _ =>
      eexists; split; [ solve [map_lookup] | ]
    | _ => straightline
    end.

  Local Ltac interaction :=
    eapply interact_mmio; [ solve [repeat straightline_with_map_lookup] | ];
    repeat straightline;
    lazymatch goal with
    | H : step _ _ _ _ _ |- _ => inversion H; clear H; subst
    end.

  Hint Extern 4 (step _ ?s _ _ _) => eapply (ReadStep s) : step.
  Hint Extern 4 (step _ ?s _ _ _) => eapply (WriteStep s) : step.
  Hint Constructors read_step : step.
  Hint Constructors write_step : step.

  Local Ltac simplify_unique_words_in H :=
    lazymatch type of H with
    | unique_words ?words =>
      let H' := fresh in
      cbv [unique_words] in H;
      pose proof (List.NoDup_dedup word.eqb words) as H';
      rewrite H in H'; clear H;
      repeat lazymatch goal with
             | H : List.NoDup [] |- _ => clear H
             | H : List.NoDup (_ :: _) |- _ => inversion H; clear H; subst; cbv [List.In] in *
             | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H
             | H : _ /\ _ |- _ => destruct H
             end
    | ?t => fail "expected hypothesis of type [unique_words _], got one of type" t
    end.

  Local Ltac one_goal_or_solved t :=
    solve [t] || (t; [ ]).

  Local Ltac invert_nobranch' H t :=
    first [ inversion H; clear H; subst; solve [t]
          | inversion H; clear H; subst; t; [ ] ].
  Local Ltac invert_nobranch H :=
    invert_nobranch' H ltac:(try congruence).

  Lemma all_reg_addrs_complete r :
    In (reg_addr r) (all_reg_addrs : list Semantics.word).
  Proof.
    assert (forall w, word.add w (word.of_Z 0) = w) as word_add_0
        by (intros; ring).
    cbv [all_reg_addrs list_reg_addrs].
    rewrite nregs_key_eq, nregs_iv_eq, nregs_data_eq.
    repeat lazymatch goal with
           | |- context [Z.to_nat ?n] =>
             let x := constr:(Z.to_nat n) in
             let y := (eval vm_compute in x) in
             change x with y
           end.
    cbn [map seq app].
    repeat lazymatch goal with
           | |- context [word.add _ (word.of_Z (?n * ?m))] =>
             let x := constr:(n * m) in
             let y := (eval vm_compute in x) in
             change x with y
           end.
    rewrite !word_add_0.
    destruct r; cbv [reg_addr In]; tauto.
  Qed.

  (* TODO: implement register naming with separation logic? e.g.

     (Register addr val * Register addr2 val2 * ...) regs

     Then inductive rules could say (Register addr val * R) regs
   *)
  Lemma reg_addr_unique r1 r2 : reg_addr r1 = reg_addr r2 -> r1 = r2.
  Proof.
    assert (forall w, word.add w (word.of_Z 0) = w) as word_add_0
        by (intros; ring).
    pose proof addrs_unique as Huniq.
    cbv [all_reg_addrs list_reg_addrs] in *.
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

  Local Ltac invert_bool :=
    lazymatch goal with
    | H : (_ && _)%bool = true |- _ =>
      apply Bool.andb_true_iff in H; destruct H
    | H : (_ && _)%bool = false |- _ =>
      apply Bool.andb_false_iff in H; destruct H
    | H : negb _ = true |- _ =>
      apply Bool.negb_true_iff in H
    | H : negb _ = false |- _ =>
      apply Bool.negb_false_iff in H
    end.

  Lemma execution_unique (t : trace) s1 s2 :
    execution t s1 ->
    execution t s2 ->
    s1 = s2.
  Proof.
    pose proof status_flags_unique_and_nonzero (ok:=consts_ok) as Hflags.
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
            | H : reg_addr _ = reg_addr _ |- _ =>
              apply reg_addr_unique in H; subst
            | H : step _ _ _ _ _ |- _ =>
              inversion H; clear H; subst
            | H : read_step _ _ _ _ |- _ =>
              inversion H; clear H; subst
            | H : write_step _ _ _ _ |- _ =>
              inversion H; clear H; subst
            | _ => first [ invert_bool
                        | progress cbn [status_matches_state
                                          is_input_reg
                                          is_output_reg] in *]
            end; try congruence).
  Qed.

  Lemma word_wrap_unsigned w : word.wrap (word.unsigned w) = word.unsigned w.
  Proof.
    pose proof (word.unsigned_range w).
    cbv [word.wrap]. apply Z.mod_small; lia.
  Qed.

  Local Ltac infer :=
    repeat match goal with
           | H : reg_addr _ _ |- _ => invert_nobranch H
           | H : read_step _ _ _ _ |- _ => invert_nobranch H
           | H : write_step _ _ _ _ |- _ => invert_nobranch H
           | H : execution _ (DONE _) |- _ => invert_nobranch H; destruct_products
           | H : step _ _ _ _ (DONE _) |- _ => invert_nobranch H
           | H1 : execution ?t _, H2 : execution ?t _ |- _ =>
             pose proof execution_unique _ _ _ H1 H2; subst;
             clear H2; one_goal_or_solved ltac:(try congruence)
           | H : BUSY _ _ = BUSY _ _ |- _ => invert_nobranch H
           | H : ?x = ?x |- _ => clear H
           end.

  Hint Rewrite word.unsigned_add word.unsigned_sub word.unsigned_mul
       word.unsigned_mulhuu word.unsigned_divu word.unsigned_and_nowrap
       word.unsigned_or_nowrap word.unsigned_xor word.unsigned_sru_nowrap
       word.unsigned_slu
       word.unsigned_ltu @word.unsigned_of_Z_0 @word.unsigned_of_Z_1
       using solve [eauto; (typeclasses eauto || lia) ] : push_unsigned.

  Lemma execution_step action args rets t s s':
    execution t s -> step action s args rets s' ->
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s'.
  Proof. intros; cbn [execution]; eauto. Qed.

  Definition boolean (w : Semantics.word) : Prop := (w = word.of_Z 0 \/ w = word.of_Z 1).

  Lemma boolean_and_1_r w :
    boolean w ->
    Z.land (word.unsigned w) 1 = if word.eqb w (word.of_Z 0)
                                 then 0
                                 else 1.
  Proof.
    rewrite word.unsigned_eqb.
    destruct 1; subst; autorewrite with push_unsigned.
    all:destruct_one_match; (reflexivity || congruence).
  Qed.

  Lemma has_size_slu w i n :
    has_size w n ->
    has_size (word.slu w i) (Z.min width (n + word.unsigned i)).
  Admitted.

  Lemma has_size_and w1 w2 n1 n2 :
    has_size w1 n1 ->
    has_size w2 n2 ->
    has_size (word.and w1 w2) (Z.min n1 n2).
  Admitted.

  Lemma has_size_or w1 w2 n1 n2 :
    has_size w1 n1 ->
    has_size w2 n2 ->
    has_size (word.or w1 w2) (Z.min n1 n2).
  Admitted.

  Lemma has_size_bool w :
    boolean w -> has_size w 1.
  Admitted.

  Lemma has_size_weaken w n m :
    has_size w n -> n <= m ->
    has_size w m.
  Admitted.

  Lemma has_size_ones w n :
    word.unsigned w = Z.ones n ->
    has_size w n.
  Admitted.

  Lemma has_size_pos w n : has_size w n -> 0 <= n.
  Proof.
    cbv [has_size]. intros.
    destr (0 <=? n); [ lia | exfalso ].
    rewrite Z.pow_neg_r in * by lia.
    lia.
  Qed.

  Hint Resolve has_size_slu has_size_and has_size_or has_size_ones has_size_bool : has_size.
  Local Ltac prove_has_size :=
    lazymatch goal with
    | |- has_size _ ?sz =>
      tryif is_evar sz
      then eauto 10 with nocore has_size
      else (eapply has_size_weaken;
            [ solve [prove_has_size] | ];
            lia)
    | |- ?g => fail "Unexpected goal for prove_has_size:" g
    end.

  Lemma size1_boolean w :
    has_size w 1 -> boolean w.
  Admitted.

  Lemma has_size_range w n :
    has_size w n -> 0 <= word.unsigned w < 2 ^ n.
  Proof. cbv [has_size]. tauto. Qed.

  Lemma is_flag_set_shift w flag :
    boolean w ->
    word.unsigned flag < width ->
    is_flag_set (word.slu w flag) flag = word.eqb w (word.of_Z 0).
  Proof.
    intro Hbool; intros; cbv [is_flag_set].
    pose proof word.width_pos.
    pose proof word.unsigned_range flag.
    assert (0 < 2 ^ word.unsigned flag < 2 ^ width)
      by (split; [ apply Z.pow_pos_nonneg
                 | apply Z.pow_lt_mono_r]; lia).
    rewrite !word.unsigned_eqb.
    autorewrite with push_unsigned.
    cbv [word.wrap].
    rewrite !Z.mod_small by
        (rewrite Z.shiftl_mul_pow2 by lia;
         destruct Hbool; subst; autorewrite with push_unsigned; lia).
    rewrite <-Z.shiftl_land. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite boolean_and_1_r by auto.
    rewrite word.unsigned_eqb.
    destruct Hbool; subst; autorewrite with push_unsigned.
    all:first [ apply Z.eqb_eq | apply Z.eqb_neq ].
    all:repeat destruct_one_match; try congruence.
    all:lia.
  Qed.

  Hint Rewrite Z.land_spec Z.lor_spec Z.lxor_spec Z.ldiff_spec Z.testbit_0_l
       using solve [eauto] : push_Ztestbit.
  Hint Rewrite Z.shiftl_spec Z.shiftr_spec Z.lnot_spec Z.ones_spec_high
       Z.ones_spec_low Z.testbit_neg_r using lia : push_Ztestbit.

  Lemma word_wrap_testbit n i :
    Z.testbit (word.wrap n) i = if i <? width then Z.testbit n i else false.
  Proof.
    cbv [word.wrap]. pose proof word.width_pos.
    rewrite Z.testbit_mod_pow2 by lia.
    destruct_one_match; reflexivity.
  Qed.
  Hint Rewrite @word_wrap_testbit using solve [eauto] : push_Ztestbit.

  Lemma word_testbit_inj w1 w2 :
    (forall i, 0 <= i < width ->
          Z.testbit (word.unsigned w1) i = Z.testbit (word.unsigned w2) i) ->
    w1 = w2.
  Proof.
    intro Hbits. apply word.unsigned_inj.
    apply Z.bits_inj; intro i.
    destr (0 <=? i); [ | rewrite !Z.testbit_neg_r by lia; reflexivity ].
    destr (i <? width); [ apply Hbits; lia | ].
    rewrite <-(word_wrap_unsigned w1).
    rewrite <-(word_wrap_unsigned w2).
    rewrite !word_wrap_testbit.
    destruct_one_match; (reflexivity || lia).
  Qed.

  Lemma Z_testbit_1_l i : Z.testbit 1 i = (i =? 0).
  Proof.
    change 1 with (Z.ones 1).
    destr (i =? 0); subst;
      [ autorewrite with push_Ztestbit; reflexivity | ].
    destr (i <? 0); autorewrite with push_Ztestbit; reflexivity.
  Qed.
  Hint Rewrite @Z_testbit_1_l using solve [eauto] : push_Ztestbit.

  Lemma testbit_has_size_high w i :
    has_size w i ->
    Z.testbit (word.unsigned w) i = false.
  Proof.
    cbv [has_size]; intros.
    destr (word.unsigned w =? 0);
      [ replace (word.unsigned w) with 0;
        autorewrite with push_Ztestbit; reflexivity | ].
    apply Z.bits_above_log2; [ lia | ].
    apply Z.log2_lt_pow2; lia.
  Qed.
  Hint Rewrite testbit_has_size_high using prove_has_size : push_Ztestbit.

  Lemma is_flag_set_or_shiftl_low w1 w2 (i flag : Semantics.word) :
    word.unsigned flag < word.unsigned i < width ->
    is_flag_set (word.or w1 (word.slu w2 i)) flag = is_flag_set w1 flag.
  Proof.
    intros; cbv [is_flag_set].
    f_equal. apply word_testbit_inj. intro n; intros.
    autorewrite with push_unsigned push_Ztestbit.
    destruct_one_match; boolsimpl; try reflexivity; [ ].
    lazymatch goal with
    | |- context [?x =? 0] => destr (x =? 0)
    end; boolsimpl; try reflexivity; [ ].
    destr (Z.testbit (word.unsigned w1) n);
      boolsimpl; try reflexivity.
    apply Z.testbit_neg_r; lia.
  Qed.

  Lemma boolean_shift_nonzero w i :
    boolean w ->
    word.unsigned i < width ->
    word.eqb (word.slu w i) (word.of_Z 0) = word.eqb w (word.of_Z 0).
  Proof.
    intro Hbool; intros.
    pose proof word.width_pos.
    pose proof word.unsigned_range i.
    assert (0 < 2 ^ word.unsigned i < 2 ^ width)
      by (split; [ apply Z.pow_pos_nonneg
                 | apply Z.pow_lt_mono_r]; lia).
    rewrite !word.unsigned_eqb.
    autorewrite with push_unsigned.
    rewrite Z.shiftl_mul_pow2 by lia.
    cbv [word.wrap].
    destruct Hbool; subst; autorewrite with push_unsigned;
      rewrite Z.mod_small by lia;
        first [ apply Z.eqb_neq | apply Z.eqb_eq ]; lia.
  Qed.

  Lemma is_flag_set_or_shiftl_high w1 w2 flag :
    boolean w2 ->
    word.unsigned flag < width ->
    has_size w1 (word.unsigned flag) ->
    is_flag_set (word.or w1 (word.slu w2 flag)) flag
    = word.eqb w2 (word.of_Z 0).
  Proof.
    intros; cbv [is_flag_set].
    rewrite <-(boolean_shift_nonzero w2 flag) by auto.
    f_equal. apply word_testbit_inj. intro n; intros.
    autorewrite with push_unsigned push_Ztestbit.
    destruct_one_match; try lia; [ ].
    repeat lazymatch goal with
           | |- ?x = ?x => reflexivity
           | |- context [?x =? 0] => destr (x =? 0); boolsimpl
           | H : boolean _ |- _ =>
             destruct H; subst; autorewrite with push_unsigned push_Ztestbit;
               boolsimpl
           | _ => congruence
           end.
  Qed.

  Lemma select_bits_id w offset mask size :
    has_size w size ->
    word.unsigned offset + size < width ->
    word.unsigned mask = Z.ones size ->
    select_bits (word.slu (word.and w mask) offset) offset mask = w.
  Proof.
    intros. cbv [select_bits].
    pose proof has_size_pos _ size ltac:(eassumption).
    pose proof word.unsigned_range offset.
    apply word_testbit_inj; intros.
    autorewrite with push_unsigned push_Ztestbit.
    rewrite Z.add_simpl_r.
    lazymatch goal with H : _ = Z.ones _ |- _ => rewrite H end.
    destr (i <? size); autorewrite with push_Ztestbit;
      boolsimpl; try reflexivity; [ ].
    destruct_one_match; boolsimpl;
      autorewrite with push_Ztestbit; reflexivity.
  Qed.

  Lemma select_bits_or_shiftl_low w1 w2 offset mask i size :
    word.unsigned mask = Z.ones size ->
    word.unsigned offset + size <= word.unsigned i < width ->
    select_bits (word.or w1 (word.slu w2 i)) offset mask
    = select_bits w1 offset mask.
  Proof.
    intros. cbv [select_bits].
    pose proof has_size_pos mask size ltac:(prove_has_size).
    pose proof word.unsigned_range offset.
    apply word_testbit_inj; intro n; intros.
    autorewrite with push_unsigned push_Ztestbit.
    lazymatch goal with H : _ = Z.ones _ |- _ => rewrite H end.
    destr (n <? size); autorewrite with push_Ztestbit;
      boolsimpl; try reflexivity; [ ].
    destruct_one_match; boolsimpl;
      autorewrite with push_Ztestbit; try reflexivity; [ ].
    rewrite (Z.testbit_neg_r (word.unsigned w2)) by lia.
    boolsimpl; reflexivity.
  Qed.

  Lemma select_bits_or_shiftl_high w1 w2 offset mask i size :
    has_size w1 (word.unsigned offset) ->
    has_size mask size ->
    word.unsigned i <= word.unsigned offset ->
    word.unsigned offset + size < width ->
    select_bits (word.or w1 (word.slu w2 i)) offset mask
    = select_bits (word.slu w2 i) offset mask.
  Proof.
    intros. cbv [select_bits].
    pose proof has_size_pos mask size ltac:(prove_has_size).
    pose proof word.unsigned_range offset.
    apply word_testbit_inj; intro n; intros.
    autorewrite with push_unsigned push_Ztestbit.
    boolsimpl. reflexivity.
  Qed.

  Lemma enum_member_size {elts size} (e : enum elts size) w :
    enum_member e w -> has_size w size.
  Proof.
    pose proof enum_size_ok e as size_ok.
    rewrite Forall_forall in size_ok.
    apply size_ok.
  Qed.

  Local Notation aes_op_t := (enum_member aes_op) (only parsing).
  Local Notation aes_mode_t := (enum_member aes_mode) (only parsing).
  Local Notation aes_key_len_t := (enum_member aes_key_len) (only parsing).

  Definition ctrl_operation (ctrl : Semantics.word) : bool :=
    is_flag_set ctrl AES_CTRL_OPERATION.
  Definition ctrl_mode (ctrl : Semantics.word) : Semantics.word :=
    select_bits ctrl AES_CTRL_MODE_OFFSET AES_CTRL_MODE_MASK.
  Definition ctrl_key_len (ctrl : Semantics.word) : Semantics.word :=
    select_bits ctrl AES_CTRL_KEY_LEN_OFFSET AES_CTRL_KEY_LEN_MASK.
  Definition ctrl_manual_operation (ctrl : Semantics.word) : bool :=
    is_flag_set ctrl AES_CTRL_MANUAL_OPERATION.

  (***** Proofs for specific functions *****)

  Definition ctrl_value
             (cfg_operation cfg_mode cfg_key_len cfg_manual_operation : Semantics.word) :=
    word.or
      (word.or
         (word.or (word.slu cfg_operation AES_CTRL_OPERATION)
                  (word.slu (word.and cfg_mode AES_CTRL_MODE_MASK) AES_CTRL_MODE_OFFSET))
         (word.slu (word.and cfg_key_len AES_CTRL_KEY_LEN_MASK) AES_CTRL_KEY_LEN_OFFSET))
      (word.slu cfg_manual_operation AES_CTRL_MANUAL_OPERATION).

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
        call function_env aes_init tr m (globals ++ args)
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

  Lemma aes_init_correct :
    program_logic_goal_for_function! aes_init.
  Proof.
    (* initial processing *)
    repeat straightline.

    (* write CTRL *)
    interaction; repeat straightline.

    (* done; prove postcondition *)
    ssplit; auto; [ ].
    pose proof operation_eq.
    pose proof mode_mask_eq.
    pose proof mode_size_pos.
    pose proof mode_offset_ok.
    pose proof key_len_mask_eq.
    pose proof key_len_size_pos.
    pose proof key_len_offset_ok.
    pose proof manual_operation_ok.
    cbv [op_size] in *.
    repeat lazymatch goal with
           | H : enum_member _ _ |- _ =>
             apply enum_member_size in H
           end.
    eexists; ssplit.
    { infer. eapply execution_step; eauto with step. }
    { cbv [ctrl_operation].
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
