Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.Word.
Import ListNotations.
Local Open Scope Z_scope.

(* Hint database for Z.testbit *)
Hint Rewrite Z.land_spec Z.lor_spec Z.lxor_spec Z.ldiff_spec Z.testbit_0_l
     using solve [eauto] : push_Ztestbit.
Hint Rewrite Z.shiftl_spec Z.shiftr_spec Z.lnot_spec Z.ones_spec_high
     Z.ones_spec_low Z.testbit_neg_r using lia : push_Ztestbit.

Section WithWord.
  Context {width} {word : word.word width} {word_ok : word.ok word}.

  (* Hint Database for simplifying expressions with word.unsigned *)
  (* N.B. Ideally this hint db would be more globally available, but word lemmas
     including [word.wrap] require a word.ok instance (although it's unused) and
     don't work properly in a global context *)
  Hint Rewrite word.unsigned_add word.unsigned_sub word.unsigned_mul
       word.unsigned_mulhuu word.unsigned_and_nowrap word.unsigned_or_nowrap
       word.unsigned_xor_nowrap word.unsigned_of_Z_0 word.unsigned_of_Z_1
       using solve [eauto] : push_unsigned.
  Hint Rewrite word.unsigned_divu word.unsigned_sru_nowrap word.unsigned_slu
       using lia : push_unsigned.

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

  Lemma word_wrap_testbit n i :
    Z.testbit (word.wrap n) i = if i <? width then Z.testbit n i else false.
  Proof.
    cbv [word.wrap]. pose proof word.width_pos.
    rewrite Z.testbit_mod_pow2 by lia.
    destruct_one_match; reflexivity.
  Qed.
  Hint Rewrite @word_wrap_testbit using solve [eauto] : push_Ztestbit.

  Lemma word_wrap_unsigned w : word.wrap (word.unsigned w) = word.unsigned w.
  Proof.
    pose proof (word.unsigned_range w).
    cbv [word.wrap]. apply Z.mod_small; lia.
  Qed.

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
  Hint Rewrite Z_testbit_1_l using solve [eauto] : push_Ztestbit.

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
  Hint Rewrite testbit_has_size_high
       using solve [eapply has_size_weaken; [ eauto | ]; lia] : push_Ztestbit.

  Lemma is_flag_set_or_shiftl_low w1 w2 (i flag : word) :
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
    pose proof has_size_pos mask size (has_size_ones mask size ltac:(eassumption)).
    pose proof word.unsigned_range offset.
    apply word_testbit_inj; intro n; intros.
    autorewrite with push_unsigned push_Ztestbit.
    lazymatch goal with H : _ = Z.ones _ |- _ => rewrite H end.
    destr (n <? size); autorewrite with push_Ztestbit;
      boolsimpl; try reflexivity; [ ].
    destruct_one_match; boolsimpl; [ | reflexivity].
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
    pose proof has_size_pos mask size ltac:(eassumption).
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

End WithWord.

(* Hint database for proving goals in the form of [has_size _ _] *)
Global Hint Resolve has_size_slu has_size_and has_size_or has_size_ones has_size_bool : has_size.

(* Tactic for proving has_size goals *)
Ltac prove_has_size :=
  lazymatch goal with
  | |- has_size _ ?sz =>
    tryif is_evar sz
    then eauto 20 with nocore has_size typeclass_instances
    else (eapply has_size_weaken;
          [ solve [prove_has_size] | ];
          lia)
  | |- ?g => fail "Unexpected goal for prove_has_size:" g
  end.
