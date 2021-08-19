Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Cava.Util.List.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.Loops.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Byte.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.letexists.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import HmacSoftware.Constants.
Require Import HmacSoftware.HmacSemantics.
Require Import HmacSoftware.Hmac.
Require Import Bedrock2Experiments.LibBase.AbsMMIOPropertiesUnique.
Require Import Bedrock2Experiments.LibBase.BitfieldProperties.
Require Import Bedrock2Experiments.LibBase.MMIOLabels.
Import Syntax.Coercions List.ListNotations HList.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(* TODO move to coqutil *)
Module byte.
  Lemma of_Z_unsigned: forall b,
    byte.of_Z (byte.unsigned b) = b.
  Proof.
    intros. eapply byte.unsigned_inj. rewrite byte.unsigned_of_Z.
    apply byte.wrap_unsigned.
  Qed.
End byte.

Module List.
  Lemma firstn_add{A: Type}(n m: nat)(l: list A):
    List.firstn (n + m) l = List.firstn n l ++ List.firstn m (List.skipn n l).
  Proof.
    rewrite <- (List.firstn_skipn n l) at 1.
    rewrite List.firstn_app.
    rewrite List.firstn_length.
    rewrite List.firstn_firstn.
    f_equal. {
      f_equal. lia.
    }
    destruct (Nat.min_spec n (List.length l)) as [(? & E) | (? & E)]; rewrite E.
    - f_equal. lia.
    - rewrite List.skipn_all2 by assumption. rewrite ?List.firstn_nil. reflexivity.
  Qed.
End List.

Lemma le_split_combine: forall bs n,
    n = List.length bs ->
    le_split n (le_combine bs) = bs.
Proof. intros. subst. apply split_le_combine. Qed.

(* bedrock2.ProgramLogic does cbv, which unfolds all constants *)
Ltac normalize_body_of_function f ::= Tactics.rdelta.rdelta f.

Section Proofs.
  Context {word: word.word 32} {mem: map.map word byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {timing: timing}.

  (* Plug in the right state machine parameters; typeclass inference struggles here *)
  Local Notation execution := (execution (M:=hmac_state_machine)).

  Infix "^+" := word.add  (at level 50, left associativity).
  Infix "^-" := word.sub  (at level 50, left associativity).
  Infix "^*" := word.mul  (at level 40, left associativity).
  Infix "^<<" := word.slu  (at level 37, left associativity).
  Infix "^>>" := word.sru  (at level 37, left associativity).
  Notation "/[ x ]" := (word.of_Z x) (* squeeze a Z into a word (beat it with a / to make it smaller) *)
                         (format "/[ x ]").
  Notation "\[ x ]" := (word.unsigned x)  (* \ is the open (removed) lid of the modulo box *)
                         (format "\[ x ]").    (* let a word fly into the large Z space *)

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Lemma invert_read_status_done_false: forall input n val s,
      read_step 4 (PROCESSING input n)
                /[TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET] val s ->
      Z.testbit \[val ^>> /[HMAC_INTR_STATE_HMAC_DONE_BIT]] 0 = false ->
      s = PROCESSING input (n - 1) /\ 0 < n.
  Proof.
    intros.
    remember /[TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET] as addr.
    inversion H; subst. 1: auto.
    exfalso. unfold HMAC_INTR_STATE_HMAC_DONE_BIT in *.
    rewrite word.unsigned_sru_nowrap in H0. 2: {
      rewrite word.unsigned_of_Z_0. reflexivity.
    }
    rewrite word.unsigned_of_Z_0 in H0.
    rewrite Z.shiftr_0_r in H0.
    congruence.
  Qed.

  Lemma invert_read_status_done_true: forall input n val s,
      read_step 4 (PROCESSING input n)
                /[TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET] val s ->
      Z.testbit \[val ^>> /[HMAC_INTR_STATE_HMAC_DONE_BIT]] 0 = true ->
      s = IDLE (sha256 input)
               {| intr_enable := /[0];
                  hmac_done := true;
                  hmac_en := false;
                  sha_en := true;
                  swap_endian := true;
                  swap_digest := false |}.
  Proof.
    intros.
    remember /[TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET] as addr.
    inversion H; subst. 2: reflexivity.
    exfalso. unfold HMAC_INTR_STATE_HMAC_DONE_BIT in *.
    rewrite word.unsigned_sru_nowrap in H0. 2: {
      rewrite word.unsigned_of_Z_0. reflexivity.
    }
    rewrite word.unsigned_of_Z_0 in H0.
    rewrite Z.shiftr_0_r in H0.
    congruence.
  Qed.

  Lemma invert_read_digest: forall b d i v s,
      0 <= \[i] < 8 ->
      read_step 4 (IDLE b d)
                (/[TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_DIGEST_7_REG_OFFSET] ^- i ^* /[4]) v s ->
      s = IDLE b d /\ v = /[le_combine (List.firstn 4 (List.skipn (Z.to_nat \[i] * 4) b))].
  Proof.
    intros.
    remember (/[TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_DIGEST_7_REG_OFFSET] ^- i ^* /[4]) as a.
    inversion H0. subst. split; [reflexivity|].
    f_equal. f_equal. f_equal. f_equal. ZnWords.
  Qed.

  (* not needed in this file directly, but needed at proof linking time to discharge
     assumption in AbsMMIOWritePropertiesUnique *)
  Lemma execution_unique (t : trace) s1 s2 :
    execution t s1 ->
    execution t s2 ->
    s1 = s2.
  Proof.
    eapply StateMachineProperties.execution_unique; intros;
      cbn [state_machine.is_initial_state state_machine.read_step state_machine.write_step
           hmac_state_machine] in *; simp.
    all: try match goal with
             | H: read_step _ _ _ _ _ |- _ => inversion H; subst; clear H
             | H: write_step _ _ _ _ _ |- _ => inversion H; subst; clear H
             end.
  Admitted.

  (* TODO move to bedrock2? *)
  Notation bytearray := (array (mem := mem) ptsto (word.of_Z 1)).
  Notation wordarray := (array (mem := mem) scalar32 (word.of_Z 4)).

  Axiom TODO: False.

  Lemma ptsto_aliasing_contradiction a b1 b2 (R: mem -> Prop) m
        (Hsep: (ptsto a b1 * ptsto a b2 * R)%sep m)
    : False.
  Proof.
    unfold sep in Hsep.
    unfold map.split, ptsto in *.
    simp.
    unfold map.disjoint in *.
    specialize (Hsepp1p0p1 a).
    rewrite !map.get_put_same in Hsepp1p0p1.
    eauto.
  Qed.

  (* Note: Often, we have a hypothesis `word.unsigned len = Z.of_nat (length l)`,
     from which word.unsigned_range gives us a bound that's even 1 tighter *)
  Lemma bytearray_max_length(a: word)(l: list byte)(R: mem -> Prop)(m: mem)
        (Hsep: (bytearray a l * R)%sep m)
    : Z.of_nat (List.length l) <= 2 ^ 32.
  Proof.
    remember (2 ^ 32) as B.
    assert (Z.of_nat (List.length l) <= B \/
            B < Z.of_nat (List.length l)) as C by lia.
    destruct C as [C | C]. 1: lia.
    exfalso.
    rewrite <- (List.firstn_nth_skipn _ (Z.to_nat B) l Byte.x00) in Hsep by lia.
    rewrite <- (List.firstn_nth_skipn _ 0 (List.firstn (Z.to_nat B) l) Byte.x00) in Hsep. 2: {
      rewrite List.firstn_length. lia.
    }
    rewrite List.firstn_O in Hsep. rewrite List.app_nil_l in Hsep.
    seprewrite_in (array_append ptsto) Hsep.
    seprewrite_in (array_append ptsto) Hsep.
    seprewrite_in (array_append ptsto) Hsep.
    seprewrite_in (array_cons ptsto) Hsep.
    seprewrite_in (array_cons ptsto) Hsep.
    eapply ptsto_aliasing_contradiction.
    use_sep_assumption.
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. 1: reflexivity.
    cancel_seps_at_indices 1%nat 0%nat. {
      f_equal.
      rewrite List.app_length. cbn [List.nth List.length].
      ZnWords.
    }
    ecancel_done.
  Qed.

  Lemma load_one_of_bytearray (addr addr': word) (values : list byte) R m
    (Hsep : sep (bytearray addr values) R m)
    : let n := Z.to_nat (word.unsigned (word.sub addr' addr)) in
      (n < List.length values)%nat ->
      Memory.load access_size.one m addr' =
      Some (word.of_Z (byte.unsigned (nth n values Byte.x00))).
  Proof.
    intros.
    rewrite <-(List.firstn_nth_skipn _ _ values Byte.x00 H) in Hsep.
    do 2 seprewrite_in (array_append ptsto) Hsep.
    seprewrite_in (array_cons ptsto) Hsep.
    seprewrite_in (array_nil ptsto) Hsep.
    rewrite firstn_length in Hsep. rewrite min_l in Hsep by lia.
    eapply load_one_of_sep.
    use_sep_assumption.
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. ZnWords.
    }
    ecancel_done.
  Qed.

  Lemma isolate_scalar32_of_bytarray: forall (addr addr': word) values,
    let n := Z.to_nat (word.unsigned (word.sub addr' addr)) in
    (n + 4 <= Datatypes.length values)%nat ->
    iff1 (bytearray addr values)
         (bytearray addr (List.firstn n values) *
          scalar32 addr' (word.of_Z (le_combine (List.firstn 4 (List.skipn n values)))) *
          bytearray (word.add addr' (word.of_Z 4)) (List.skipn (n + 4) values))%sep.
  Proof.
    intros.
    rewrite <- (List.firstn_skipn n values) at 1.
    rewrite <- (List.firstn_skipn 4 (List.skipn n values)) at 1.
    do 2 rewrite (array_append ptsto).
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      unfold scalar32, truncated_word, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
      f_equal. 1: ZnWords.
      replace (bytes_per (width:=32) access_size.four)
        with (Datatypes.length (List.firstn 4 (List.skipn n values))). 2: {
        rewrite List.firstn_length. rewrite min_l. 1: reflexivity.
        rewrite List.skipn_length. lia.
      }
      rewrite word.unsigned_of_Z_nowrap. 2: {
        match goal with
        | |- context[le_combine ?x] =>
          pose proof (le_combine_bound x) as P
        end.
        rewrite List.firstn_length in P. rewrite min_l in P by ZnWords.
        exact P.
      }
      remember (List.firstn 4 (List.skipn n values)) as l.
      assert (List.length l = 4%nat) as HL. {
        subst l. rewrite List.firstn_length. rewrite min_l. 1: reflexivity.
        rewrite List.skipn_length. lia.
      }
      rewrite <- (le_split_combine _ 4) at 1. 2: {
        symmetry. exact HL.
      }
      destruct l as [|b0 l]. 1: discriminate HL.
      destruct l as [|b1 l]. 1: discriminate HL.
      destruct l as [|b2 l]. 1: discriminate HL.
      destruct l as [|b3 l]. 1: discriminate HL.
      destruct l as [|b4 l]. 2: discriminate HL.
      clear HL.
      reflexivity.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal.
      - rewrite ?List.firstn_length. rewrite List.skipn_length. ZnWords.
      - rewrite List.skipn_skipn. f_equal. lia.
    }
    ecancel_done.
  Qed.

  Lemma load_four_of_bytearray (addr addr': word) (values : list byte) R m
    (Hsep : sep (bytearray addr values) R m)
    : let n := Z.to_nat (word.unsigned (word.sub addr' addr)) in
      (n + 4 <= List.length values)%nat ->
      Memory.load access_size.four m addr' =
      Some (word.of_Z (le_combine (List.firstn 4 (List.skipn n values)))).
  Proof.
    intros.
    eapply load_four_of_sep_32bit. 1: reflexivity.
    seprewrite_in isolate_scalar32_of_bytarray Hsep. 1: subst n; eassumption.
    ecancel_assumption.
  Qed.

  Lemma store_four_to_bytearray (addr addr' v: word) (values : list byte) R m (post: mem -> Prop):
    sep (bytearray addr values) R m ->
    let n := Z.to_nat (word.unsigned (word.sub addr' addr)) in
    (n + 4 <= List.length values)%nat ->
    (forall m', sep (bytearray addr (List.upds values n (le_split 4 (word.unsigned v)))) R m' ->
               post m') ->
    exists m', Memory.store access_size.four m addr' v = Some m' /\ post m'.
  Proof.
    intros Hsep n HL HPost.
    eapply store_four_of_sep.
    - seprewrite_in isolate_scalar32_of_bytarray Hsep. 1: subst n; eassumption.
      ecancel_assumption.
    - clear dependent m. intros m Hsep. eapply HPost.
      SeparationLogic.seprewrite isolate_scalar32_of_bytarray. {
        rewrite List.upds_length. subst n. exact HL.
      }
      use_sep_assumption.
      cancel.
      unfold List.upds. change (Z.to_nat \[addr' ^- addr]) with n.
      pose proof (length_le_split 4 \[v]).
      cancel_seps_at_indices 0%nat 1%nat. {
        f_equal.
        autorewrite with listsimpl push_skipn push_firstn push_length.
        rewrite le_combine_split.
        change (Z.of_nat 4 * 8) with 32.
        rewrite word.wrap_unsigned.
        rewrite word.of_Z_unsigned.
        reflexivity.
      }
      cancel_seps_at_indices 0%nat 0%nat. {
        f_equal.
        (* TODO this kind of list simplification should be automated *)
        rewrite firstn_app.
        rewrite (@List.firstn_all2 _ n (List.firstn n values)). 2: {
          rewrite List.firstn_length. lia.
        }
        rewrite List.firstn_length.
        replace (n - Init.Nat.min n (Datatypes.length values))%nat with O by lia.
        rewrite List.firstn_O.
        rewrite List.app_nil_r.
        reflexivity.
      }
      cancel_seps_at_indices 0%nat 0%nat. {
        f_equal.
        rewrite List.skipn_app.
        rewrite (List.skipn_all (n + 4) (List.firstn n values)). 2: {
          rewrite List.firstn_length. lia.
        }
        rewrite List.app_nil_l.
        rewrite List.firstn_length.
        replace (n + 4 - Init.Nat.min n (Datatypes.length values))%nat with 4%nat by lia.
        rewrite List.skipn_app.
        rewrite (List.skipn_all 4 (List.firstn (Datatypes.length values - n) (le_split 4 \[v]))). 2: {
          rewrite List.firstn_length. rewrite length_le_split. lia.
        }
        rewrite List.app_nil_l.
        rewrite List.skipn_skipn.
        f_equal.
        rewrite List.firstn_length.
        rewrite length_le_split.
        lia.
      }
      ecancel_done.
  Qed.

  Lemma Zlandb: forall (b1 b2: bool),
      Z.land (if b1 then 1 else 0) (if b2 then 1 else 0) = if (andb b1 b2) then 1 else 0.
  Proof. destruct b1; destruct b2; reflexivity. Qed.

  Lemma then1_else0_nonzero: forall b: bool,
      (if b then 1 else 0) <> 0 -> b = true.
  Proof. destruct b; congruence. Qed.

  Lemma then1_else0_zero: forall b: bool,
      (if b then 1 else 0) = 0 -> b = false.
  Proof. destruct b; congruence. Qed.

  Lemma Zland_ones_to_mod: forall a ones,
      ones = Z.ones (Z.log2_up ones) ->
      Z.land a ones = a mod 2 ^ (Z.log2_up ones).
  Proof.
    intros. rewrite <- Z.land_ones. 2: apply Z.log2_up_nonneg.
    f_equal. exact H.
  Qed.

  Lemma Zland_pow2_to_testbit: forall a pow2,
      pow2 = 2 ^ (Z.log2_up pow2) ->
      Z.land a pow2 = if Z.testbit a (Z.log2_up pow2) then pow2 else 0.
  Proof.
    intros.
    eapply Z.bits_inj'. intros.
    rewrite Z.land_spec.
    rewrite prove_Zeq_bitwise.testbit_if.
    rewrite H at 1.  rewrite H at 3.
    rewrite Z.pow2_bits_eqb by apply Z.log2_up_nonneg.
    rewrite Z.testbit_0_l.
    destr (Z.eqb (Z.log2_up pow2) n).
    + subst n. destruct (Z.testbit a (Z.log2_up pow2)); reflexivity.
    + rewrite Bool.andb_false_r. destr (Z.testbit a (Z.log2_up pow2)); reflexivity.
  Qed.

  Ltac simpl_conditional :=
    match goal with
    | H: _ /\ _ |- _ => destruct H
    | H: _ |- _ => rewrite Zlandb in H
    | H: word.eqb ?x ?y = true  |- _ => apply (word.eqb_true  x y) in H
    | H: word.eqb ?x ?y = false |- _ => apply (word.eqb_false x y) in H
    | H: andb ?b1 ?b2 = true |- _ => apply (Bool.andb_true_iff b1 b2) in H
    | H: andb ?b1 ?b2 = false |- _ => apply (Bool.andb_false_iff b1 b2) in H
    | H: orb ?b1 ?b2 = true |- _ => apply (Bool.orb_true_iff b1 b2) in H
    | H: orb ?b1 ?b2 = false |- _ => apply (Bool.orb_false_iff b1 b2) in H
    | H: _ |- _ => rewrite word.unsigned_and_nowrap in H
    | H: _ |- _ => rewrite word.unsigned_if in H
    | H: _ |- _ => rewrite word.unsigned_eqb in H
    | H: _ |- _ => rewrite word.unsigned_ltu in H
    | H: _ |- _ => rewrite word.unsigned_of_Z_small in H by
          (lazymatch goal with
           | |- _ <= ?x < 2 ^ _ =>
             lazymatch isZcst x with true => cbv; intuition discriminate end
           end)
    | H: _ |- _ => apply then1_else0_nonzero in H
    | H: _ |- _ => apply then1_else0_zero in H
    | H: Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    | H: Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
    | H: Z.ltb _ _ = true |- _ => eapply Z.ltb_lt in H
    | H: Z.ltb _ _ = false |- _ => eapply Z.ltb_ge in H
    | H: context[Z.land ?a ?ones] |- _ =>
      lazymatch isZcst ones with true => idtac end;
      let m := eval cbv in (2 ^ Z.log2_up ones) in
      rewrite (Zland_ones_to_mod a ones eq_refl: _ = a mod m) in H
    | H: context[Z.land ?a ?pow2] |- _ =>
      let i := lazymatch isZcst pow2 with
               | true => eval cbv in (Z.log2_up pow2)
               | false => lazymatch pow2 with
                          | 2 ^ ?m => m
                          end
               end in
      rewrite (Zland_pow2_to_testbit a pow2 eq_refl:
                 Z.land a pow2 = if Z.testbit a i then pow2 else 0) in H
    | H: word.unsigned (if ?b then _ else _) = 0 |- _ => apply word.if_zero in H
    | H: word.unsigned (if ?b then _ else _) <> 0 |- _ => apply word.if_nonzero in H
    end.

  Ltac simpl_conditionals := repeat simpl_conditional.

  Global Instance spec_of_hmac_sha256_init : spec_of b2_hmac_sha256_init :=
    fun function_env =>
      forall tr m (R : mem -> Prop) (digest_buffer: list byte) (d: idle_data),
      R m ->
      execution tr (IDLE digest_buffer d) ->
      call function_env b2_hmac_sha256_init tr m []
        (fun tr' m' rets =>
            rets = [] /\ execution tr' (CONSUMING []) /\ R m').
  Lemma hmac_sha256_init_correct :
    program_logic_goal_for_function! b2_hmac_sha256_init.
  Proof.
    repeat straightline.
    straightline_call. 1: reflexivity. 1: eapply write_cfg. 1: eassumption.
    repeat straightline.
    straightline_call. 1: reflexivity. 1: eapply write_intr_enable. 1: eassumption.
    cbn [intr_enable hmac_done hmac_en sha_en swap_endian swap_digest] in *.
    repeat straightline.
    straightline_call. 1: reflexivity. 1: eapply write_intr_state. 1: eassumption.
    cbn [intr_enable hmac_done hmac_en sha_en swap_endian swap_digest] in *.
    repeat straightline.
    straightline_call.
    repeat straightline.
    straightline_call.
    repeat straightline.
    straightline_call.
    repeat straightline.
    straightline_call.
    repeat straightline.
    straightline_call. 1: reflexivity. 1: eapply write_cfg. 1: eassumption.
    repeat straightline.
    straightline_call.
    repeat straightline.
    cbn [intr_enable hmac_done hmac_en sha_en swap_endian swap_digest] in *.
    straightline_call. 1: reflexivity. 1: eapply write_hash_start. {
      (* bitfiddling *)
      case TODO.
    }
    { match goal with
      | H: execution ?t ?s1 |- execution ?t ?s2 => replace s2 with s1; [exact H|]
      end.
      f_equal. f_equal.
      (* bitfiddling *)
      all: case TODO.
    }
    repeat straightline.
    ssplit; eauto.
  Qed.

  Global Instance spec_of_hmac_sha256_update : spec_of b2_hmac_sha256_update :=
    fun function_env =>
      forall tr m (R : mem -> Prop) (previous_input new_input: list byte) data_addr len,
      word.unsigned len = Z.of_nat (length new_input) ->
      data_addr <> word.of_Z 0 ->
      (bytearray data_addr new_input * R)%sep m ->
      execution tr (CONSUMING previous_input) ->
      call function_env b2_hmac_sha256_update tr m [data_addr; len]
        (fun tr' m' rets =>
           rets = [word.of_Z Constants.kErrorOk] /\
           execution tr' (CONSUMING (previous_input ++ new_input)) /\
           (bytearray data_addr new_input * R)%sep m').

  Lemma hmac_sha256_update_correct :
    program_logic_goal_for_function! b2_hmac_sha256_update.
  Proof.
    repeat straightline.
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    repeat straightline.
    subst v.
    rewrite word.unsigned_if.
    rewrite word.eqb_ne by assumption.
    rewrite word.unsigned_of_Z_0.
    split; intros E. 1: exfalso; apply E; reflexivity.
    clear E.
    repeat straightline.
    set (data_aligned := word.of_Z (word.unsigned (word.add data_addr (word.of_Z 3)) / 4 * 4)).
    rename fifo_reg into fifo_reg0, len into len0.

    (* first while loop: *)
    eapply (while ["fifo_reg"; "data_sent"; "data"; "len"]
                  (fun measure t m fifo_reg data_sent data len =>
                     data_addr = data /\
                     fifo_reg = fifo_reg0 /\
                     data_sent ^+ /[measure] = data_aligned /\
                     0 <= measure < 4 /\
                     \[data_sent ^- data_addr] + \[len] = Z.of_nat (List.length new_input) /\
                     (bytearray data_addr new_input * R)%sep m /\
                     execution t (CONSUMING (previous_input ++
                        List.firstn (Z.to_nat \[data_sent ^- data_addr]) new_input)))
                  (Z.lt_wf 0)
                  \[data_aligned ^- data_addr]).
    1: repeat straightline.
    { (* invariant holds initially: *)
      loop_simpl.
      replace (Z.to_nat \[data_addr ^- data_addr]) with 0%nat by ZnWords.
      change (@List.firstn ?A 0 _) with (@nil A).
      rewrite List.app_nil_r.
      ssplit; try assumption; try ZnWords. }
    loop_simpl.
    intros measure t m0 fifo_reg data_sent data len. (* TODO derive names automatically *)
    repeat straightline.
    { (* if br is true, running first loop body again satisfies invariant *)
      subst br.
      simpl_conditionals.
      eexists. split. {
        repeat straightline.
        eexists. split.
        { eapply load_one_of_bytearray. 1: eassumption. ZnWords. }
        repeat straightline.
      }
      straightline_call.
      { cbv [state_machine.reg_addr hmac_state_machine id]. reflexivity. }
      2: eassumption.
      { eapply write_byte. 2: reflexivity.
        match goal with
        | |- context[byte.unsigned ?x] => pose proof (byte.unsigned_range x)
        end.
        ZnWords. }
      repeat straightline.
      cbv [Markers.unique Markers.split].
      eexists (measure - 1). ssplit; trivial; try ZnWords.
      subst a.
      eapply execution_step_write with (sz := 1%nat). 1: eassumption. 1: reflexivity.
      cbv [state_machine.write_step hmac_state_machine].
      replace (Z.to_nat \[data_sent ^- data]) with
              (S (Z.to_nat \[data_sent0 ^- data])) by ZnWords.
      rewrite <- (List.firstn_nth _ _ _ Byte.x00) by ZnWords.
      rewrite List.app_assoc.
      match goal with
      | |- context[byte.unsigned ?x] => pose proof (byte.unsigned_range x)
      end.
      eapply write_byte. 1: ZnWords.
      f_equal. f_equal.
      rewrite word.unsigned_of_Z_small by ZnWords.
      rewrite byte.of_Z_unsigned.
      reflexivity.
    }
    (* if br is false, code after first loop is correct: *)
    subst br.
    simpl_conditionals.
    match goal with
    | H: _ \/ _ |- _ => destruct H as [A | A]; simpl_conditionals
    end.
    { (* if the first loop was ended because len=0, the remaining two loops are skipped: *)
      eapply while_zero_iterations. {
        repeat straightline.
        subst v.
        rewrite word.unsigned_ltu.
        apply word.unsigned_inj.
        rewrite word.unsigned_if.
        destruct_one_match; ZnWords.
      }
      repeat straightline.
      eapply while_zero_iterations. {
        repeat straightline. ZnWords.
      }
      repeat straightline.
      ssplit. 1: reflexivity. 2: eassumption.
      match goal with
      | H: execution ?t ?s1 |- execution ?t ?s2 =>
        replace s2 with s1; [exact H|]
      end.
      f_equal. f_equal. rewrite List.firstn_all2. 1: reflexivity. ZnWords.
    }
    (* if the first loop was ended because `data_sent & 3 == 0`,
       we have to step through the remaining two loops as well: *)
    assert (data_sent = data_aligned) by ZnWords. subst data_sent.
    clear dependent tr.
    clear dependent measure.
    clear dependent m.
    match goal with
    | H: word.unsigned ?L = Z.of_nat (List.length new_input) |- _ =>
      pose proof (word.unsigned_range L) as LB;
      rewrite H in LB;
      clear dependent L
    end.
    rename data into data_addr, t into tr, len into len0.

    (* second while loop: *)
    eapply (while ["fifo_reg"; "data_sent"; "data"; "len"]
                  (fun measure t m fifo_reg data_sent data len =>
                     data_addr = data /\
                     fifo_reg = fifo_reg0 /\
                     measure = \[len] /\
                     \[data_sent] mod 4 = 0 /\
                     \[data_sent ^- data_addr] + \[len] = Z.of_nat (List.length new_input) /\
                     (bytearray data_addr new_input * R)%sep m /\
                     execution t (CONSUMING (previous_input ++
                        List.firstn (Z.to_nat \[data_sent ^- data_addr]) new_input)))
                  (Z.lt_wf 0)
                  \[len0]).
    1: repeat straightline.
    { (* invariant holds initially: *)
      loop_simpl.
      ssplit; try assumption; try ZnWords. }
    loop_simpl.
    intros measure t m fifo_reg data_sent data len. (* TODO derive names automatically *)
    repeat straightline.
    { (* if br is true, running first loop body again satisfies invariant *)
      subst br.
      simpl_conditionals.
      eexists. split. {
        repeat straightline.
        eexists. split.
        { eapply load_four_of_bytearray. 1: eassumption. ZnWords. }
        repeat straightline.
      }
      straightline_call.
      { cbv [state_machine.reg_addr hmac_state_machine id]. reflexivity. }
      2: eassumption.
      1: eapply write_word. 1: reflexivity.
      repeat straightline.
      cbv [Markers.unique Markers.split].
      eexists (measure - 4). ssplit; trivial; try ZnWords.
      subst a.
      eapply execution_step_write with (sz := 4%nat). 1: eassumption. 1: reflexivity.
      cbv [state_machine.write_step hmac_state_machine].
      eapply write_word. rewrite <- List.app_assoc. f_equal.
      subst data_sent.
      match goal with
      | |- context[le_combine ?x] =>
        pose proof (le_combine_bound x) as P
      end.
      rewrite List.firstn_length in P. rewrite min_l in P by ZnWords.
      rewrite word.unsigned_of_Z_small by ZnWords.
      rewrite le_split_combine. 2: {
        rewrite List.firstn_length. ZnWords.
      }
      replace (Z.to_nat \[data_sent0 ^+ /[4] ^- data])
        with (Z.to_nat \[data_sent0 ^- data] + 4)%nat by ZnWords.
      apply List.firstn_add.
    }
    (* if br is false, code after second loop is correct: *)
    subst br.
    simpl_conditionals.
    clear dependent tr.
    clear dependent m0.
    clear dependent len0.
    rename data_sent into data_aligned_last.
    rename data into data_addr, t into tr, len into len0.
    set (data_past_end := data_addr ^+ /[Z.of_nat (List.length new_input)]).

    (* third while loop: *)
    eapply (while ["fifo_reg"; "data_sent"; "data"; "len"]
                  (fun measure t m fifo_reg data_sent data len =>
                     data_addr = data /\
                     fifo_reg = fifo_reg0 /\
                     measure = \[len] /\
                     0 <= measure < 4 /\
                     \[data_sent ^- data_addr] + \[len] = Z.of_nat (List.length new_input) /\
                     (bytearray data_addr new_input * R)%sep m /\
                     execution t (CONSUMING (previous_input ++
                        List.firstn (Z.to_nat \[data_sent ^- data_addr]) new_input)))
                  (Z.lt_wf 0)
                  \[len0]).
    1: repeat straightline.
    { (* invariant holds initially: *)
      loop_simpl.
      ssplit; try assumption; try ZnWords. }
    loop_simpl.
    intros measure t m0 fifo_reg data_sent data len. (* TODO derive names automatically *)
    repeat straightline.
    { (* if break condition is true, running third loop body again satisfies invariant *)
      simpl_conditionals.
      eexists. split. {
        repeat straightline.
        eexists. split.
        { eapply load_one_of_bytearray. 1: eassumption. ZnWords. }
        repeat straightline.
      }
      straightline_call.
      { cbv [state_machine.reg_addr hmac_state_machine id]. reflexivity. }
      2: eassumption.
      { eapply write_byte. 2: reflexivity.
        match goal with
        | |- context[byte.unsigned ?x] => pose proof (byte.unsigned_range x)
        end.
        ZnWords. }
      repeat straightline.
      cbv [Markers.unique Markers.split].
      eexists (measure - 1). ssplit; trivial; try ZnWords.
      subst a.
      eapply execution_step_write with (sz := 1%nat). 1: eassumption. 1: reflexivity.
      cbv [state_machine.write_step hmac_state_machine].
      replace (Z.to_nat \[data_sent ^- data]) with
              (S (Z.to_nat \[data_sent0 ^- data])) by ZnWords.
      rewrite <- (List.firstn_nth _ _ _ Byte.x00) by ZnWords.
      rewrite List.app_assoc.
      match goal with
      | |- context[byte.unsigned ?x] => pose proof (byte.unsigned_range x)
      end.
      eapply write_byte. 1: ZnWords.
      f_equal. f_equal.
      rewrite word.unsigned_of_Z_small by ZnWords.
      rewrite byte.of_Z_unsigned.
      reflexivity.
    }
    (* if break condition is false, `result = kErrorOk` is run and now we have to prove
       the postcondition of the function: *)
    split; [reflexivity|].
    split; [|eassumption].
    match goal with
    | H: execution ?t ?s |- execution ?t ?s' => replace s' with s; [exact H|]
    end.
    f_equal. f_equal.
    apply List.firstn_all2.
    ZnWords.
  Qed.

  Global Instance spec_of_hmac_sha256_final : spec_of b2_hmac_sha256_final :=
    fun function_env =>
      forall tr (m: mem) (R : mem -> Prop)
             (input digest_trash: list Byte.byte) (digest_addr: word),
      Z.of_nat (length digest_trash) = 32 ->
      digest_addr <> word.of_Z 0 ->
      (bytearray digest_addr digest_trash * R)%sep m ->
      execution tr (CONSUMING input) ->
      call function_env b2_hmac_sha256_final tr m [digest_addr]
        (fun tr' (m': mem) rets =>
           rets = [word.of_Z Constants.kErrorOk] /\
           execution tr' (IDLE (sha256 input) (* digest has been read, but still in device *)
                            {| hmac_done := false; (* done flag was already cleared by this function *)
                               intr_enable := word.of_Z 0;
                               hmac_en := false;
                               sha_en := true;
                               swap_endian := true;
                               swap_digest := false; |}) /\
           (* digest has been stored at correct memory location: *)
           (bytearray digest_addr (sha256 input) * R)%sep m').

  Lemma hmac_sha256_final_correct :
    program_logic_goal_for_function! b2_hmac_sha256_final.
  Proof.
    repeat straightline.
    assert (List.length (sha256 input) = 32)%nat by case TODO.
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    repeat straightline.
    subst v.
    rewrite word.unsigned_if.
    rewrite word.eqb_ne by assumption.
    rewrite word.unsigned_of_Z_0.
    split; intros E. 1: exfalso; apply E; reflexivity.
    clear E.
    repeat straightline.
    straightline_call.
    repeat straightline.
    straightline_call. 1: reflexivity. 1: eapply write_hash_process. 2: eassumption.
    { case TODO. (* bitfiddling *) }
    repeat straightline.
    subst done.

    (* first while loop *)
    eapply atleastonce with (variables := ["digest"; "reg"; "done"])
             (invariant := fun measure t m digest reg done =>
               digest = digest_addr /\
               execution t (PROCESSING input measure) /\
               (bytearray digest_addr digest_trash ⋆ R)%sep m).
    { repeat straightline. }
    { eapply (Z.lt_wf 0). }
    { (* if condition initially is false, that's a contradiction, so we don't need to prove post: *)
      repeat straightline. subst br. simpl_conditionals. exfalso. eauto. }
    { (* invariant holds initially *)
      loop_simpl. eauto. }
    loop_simpl.
    (* step through first loop body: *)
    repeat straightline.
    straightline_call. 1: reflexivity. {
      (* to show that there exists at least one valid read step, we pick read_done_bit_done,
         but the device could also choose read_done_bit_not_done, so later we'll have to treat
         both cases *)
      eapply read_done_bit_done with (v0 := /[1]).
      rewrite word.unsigned_of_Z_1. reflexivity.
    }
    1: eassumption.
    repeat straightline.
    straightline_call.
    (* TODO here we see that `x3 x4 x5 : word` should be named `"digest" "reg" "done"`,
       respectively, automate this naming *)
    repeat straightline.
    { (* loop condition is true: need to show that invariant still holds with smaller measure *)
      subst br.
      rename x5 into done. subst done.
      simpl_conditionals.
      eexists (v - 1).
      edestruct invert_read_status_done_false; [eassumption..|].
      subst x.
      split; [auto|lia]. }
    (* loop condition is false: need to show that code after first loop is correct *)
    subst br. simpl_conditionals.
    eassert (x = _). {
      eapply invert_read_status_done_true; eassumption.
    }
    subst x.
    straightline_call. 1: reflexivity. 1: eapply write_intr_state. 1: eassumption.
    cbn [intr_enable hmac_done hmac_en sha_en swap_endian swap_digest] in *.
    repeat straightline.

    clear dependent reg.
    repeat match goal with
           | H: execution ?t1 _ |- cmd _ _ ?t2 _ _ _ =>
             tryif unify t1 t2 then fail else clear H
           end.
    repeat match goal with
           | m1: @map.rep _ _ mem |- cmd _ _ _ ?m2 _ _ =>
             tryif unify m1 m2 then fail else clear dependent m1
           end.
    rename a3 into tr.
    clear dependent v.
    match goal with
    | H: Z.testbit \[_ ^>> _] 0 = true |- _ => rename H into T
    end.
    unfold HMAC_INTR_STATE_HMAC_DONE_BIT in *.
    rewrite word.unsigned_sru_nowrap in T. 2: {
      rewrite word.unsigned_of_Z_0. reflexivity.
    }
    rewrite word.unsigned_of_Z_0 in T.
    rewrite Z.shiftr_0_r in T.
    rewrite T in *.

    (* second while loop: *)
    eapply (while ["digest"; "reg"; "done"; "i"]
                  (fun remaining t m digest reg done i =>
                     execution t (IDLE (sha256 input)
                                       {| intr_enable := /[0];
                                          hmac_done := false;
                                          hmac_en := false;
                                          sha_en := true;
                                          swap_endian := true;
                                          swap_digest := false
                                       |}) /\
                     0 <= \[i] <= 8 /\
                     0 <= remaining <= 32 /\
                     4 * \[i] + remaining = 32 /\
                     digest = digest_addr /\
                     (bytearray digest (List.firstn (Z.to_nat (4 * \[i])) (sha256 input) ++
                                        List.skipn (Z.to_nat (4 * \[i])) digest_trash) * R)%sep m)
                  (Z.lt_wf 0) 32).
    { repeat straightline. }
    { (* invariant holds initially: *)
      loop_simpl. subst i. rewrite word.unsigned_of_Z_0.
      ssplit; try reflexivity; try assumption; try lia. }
    loop_simpl.
    repeat straightline.
    { (* running loop body satisfies invariant *)
      subst br. simpl_conditionals. subst i. rename x5 into i.
      straightline_call. 1: reflexivity. 2: eassumption. 1: eapply read_digest with (i0 := \[i]).
      all: try reflexivity.
      1-2: ZnWords.
      repeat straightline.
      eapply store_four_to_bytearray. 1: ecancel_assumption.
      { subst a2. rewrite List.app_length. rewrite List.firstn_length. rewrite List.skipn_length.
        ZnWords_pre.
        Z.div_mod_to_equations.
        (* Note: On Coq master of Aug 12, 2021, this goal is just solved by `lia`, but
           with Coq 8.13.2, `lia` hangs, so we need more manual steps: *)
        assert (2 ^ 32 <> 0) as NZ by (clear; lia).
        repeat match goal with
               | H: 2 ^ 32 = 0 -> _ |- _ => clear H
               | H: 2 ^ 32 < 0 -> _ |- _ => clear H
               | H: 0 < 2 ^ 32 -> _ |- _ => specialize (H eq_refl)
               | H: 2 ^ 32 <> 0 -> _ |- _ => specialize (H NZ)
               end.
        subst.
        clear H NZ.
        clear dependent word.
        Zify.zify.
        repeat match goal with
               | H: _ /\ _ |- _ => destruct H
               | H: _ \/ _ |- _ => destruct H
               end;
        lia.
      }
      intros m Hm.
      repeat straightline.
      exists (v - 4).
      split; [|lia].
      split. {
        subst a.
        eapply execution_step_read with (sz := 4%nat). 1: eassumption. 1: reflexivity.
        cbn [state_machine.read_step hmac_state_machine] in *.
        match goal with
        | H: read_step 4 ?s ?a ?v ?s1 |- read_step 4 ?s ?a ?v ?s2 =>
          replace s2 with s1 at 2; [exact H|]
        end.
        eapply invert_read_digest with (i := i0). 1: lia. 1: eassumption.
      }
      split; [ZnWords|].
      split; [ZnWords|].
      split; [ZnWords|].
      split; [reflexivity|].
      use_sep_assumption.
      cancel.
      cancel_seps_at_indices 0%nat 0%nat. {
        f_equal.
        rewrite List.upds_app2. 2: {
          rewrite List.firstn_length.
          (* Note: `ZnWords` should just work here, but when it calls `lia`, `lia` hangs. *)
          subst a2. rewrite H9. revert dependent v. clear -word_ok. intros.
          pose proof word.unsigned_range i0.
          replace (Init.Nat.min (Z.to_nat (4 * \[i0])) 32) with (Z.to_nat (4 * \[i0])) by lia.
          replace \[digest_addr ^+ i0 ^* /[4] ^- digest_addr] with \[i0 ^* /[4]] by ZnWords.
          ZnWords.
        }
        subst i.
        replace (Z.to_nat (4 * \[i0 ^+ /[1]])) with (Z.to_nat (4 * \[i0]) + 4)%nat by ZnWords.
        rewrite List.firstn_add. rewrite <- List.app_assoc.
        f_equal.
        unfold List.upds.
        rewrite ?List.firstn_length.
        replace (Z.to_nat \[a2 ^- digest_addr] -
                 Init.Nat.min (Z.to_nat (4 * \[i0])) (Datatypes.length (sha256 input)))%nat
          with 0%nat.
        2: {
          (* Note: `ZnWords` should just work here, but when it calls `lia`, `lia` hangs. *)
          subst a2. rewrite H9. revert dependent v. clear -word_ok. intros.
          pose proof word.unsigned_range i0.
          replace (Init.Nat.min (Z.to_nat (4 * \[i0])) 32) with (Z.to_nat (4 * \[i0])) by lia.
          replace \[digest_addr ^+ i0 ^* /[4] ^- digest_addr] with \[i0 ^* /[4]] by ZnWords.
          ZnWords.
        }
        rewrite List.firstn_O. rewrite List.app_nil_l.
        rewrite Nat.add_0_r, Nat.sub_0_r.
        rewrite List.skipn_length.
        edestruct invert_read_digest as (_ & E). 2: eassumption. 1: ZnWords. subst.
        rewrite word.unsigned_of_Z_nowrap. 2: {
          match goal with
          | |- context[le_combine ?x] =>
            pose proof (le_combine_bound x) as P
          end.
          rewrite List.firstn_length in P. rewrite min_l in P by ZnWords.
          exact P.
        }
        rewrite le_split_combine. 2: {
          rewrite List.firstn_length. ZnWords.
        }
        rewrite List.firstn_firstn.
        replace (Init.Nat.min (Datatypes.length digest_trash - Z.to_nat (4 * \[i0])) 4) with 4%nat
          by ZnWords.
        f_equal.
        - f_equal. f_equal. ZnWords.
        - rewrite List.firstn_length. rewrite List.skipn_length.
          rewrite List.skipn_skipn. f_equal. ZnWords.
      }
      ecancel_done.
    }
    (* postcondition holds at end  *)
    subst br. simpl_conditionals. subst i. rename x5 into i.
    replace (4 * \[i]) with 32 in * by ZnWords.
    rewrite List.firstn_all2 in * by ZnWords.
    rewrite List.skipn_all2 in * by ZnWords.
    rewrite List.app_nil_r in *.
    subst result.
    auto.
  Qed.

End Proofs.
