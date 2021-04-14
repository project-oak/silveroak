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
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Import Syntax.Coercions List.ListNotations.
Local Open Scope Z_scope.

Section Proofs.
  Context {p : parameters} {p_ok : parameters.ok p}
          {consts : constants word.rep} {consts_ok : constants.ok consts}
          {timing : timing}.
  Import constants parameters.

  Existing Instance constants.constant_names | 10.

  (* plug in implicits (otherwise [straightline] fails) *)
  Definition put_wait_get := put_wait_get.

  Instance spec_of_put_wait_get : spec_of put_wait_get :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) input,
        (* no special requirements of the memory *)
        R m ->
        (* circuit must start in IDLE state *)
        execution tr IDLE ->
        let args := [input] in
        call function_env put_wait_get tr m (globals ++ args)
             (fun tr' m' rets =>
                (* the circuit is back in IDLE state *)
                execution tr' IDLE
                (* ...and the same properties as before hold on the memory *)
                /\ R m'
                (* ...and output matches spec *)
                /\ rets = [proc input]).

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
  Hint Constructors reg_addr : step.
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

  Lemma execution_unique (t : trace) s1 s2 :
    execution t s1 ->
    execution t s2 ->
    s1 = s2.
  Proof.
    pose proof addrs_unique (ok:=consts_ok).
    pose proof flags_unique_and_nonzero (ok:=consts_ok) as Hflags.
    cbv [map] in Hflags.
    simplify_unique_words_in Hflags.
    revert s1 s2.
    induction t; cbn [execution]; [ congruence | ].
    intros; destruct_products.
    match goal with
    | H1 : execution t ?s1, H2 : execution t ?s2 |- _ =>
      specialize (IHt _ _ H1 H2); subst
    end.
    repeat lazymatch goal with
           | |- ?x = ?x => reflexivity
           | H : reg_addr _ _ |- _ =>
             inversion H; clear H; subst; try congruence
           | H : step _ _ _ _ _ |- _ =>
             inversion H; clear H; subst
           | H : read_step _ _ _ _ |- _ =>
             inversion H; clear H; subst
           | H : write_step _ _ _ _ |- _ =>
             inversion H; clear H; subst
           | _ => cbv [status_flag status_value] in *; congruence
           end.
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
       word.unsigned_mulhuu word.unsigned_divu word.unsigned_and
       word.unsigned_or word.unsigned_xor word.unsigned_sru word.unsigned_slu
       word.unsigned_ltu @word.unsigned_of_Z_0 @word.unsigned_of_Z_1
       using solve [typeclasses eauto] : push_unsigned.

  (* (status value STATUS_DONE) & (1 << STATUS_DONE) = 0 *)
  Lemma check_done_flag :
    word.unsigned
      (if
          word.eqb (word.and (status_value STATUS_DONE)
                             (word.slu (word.of_Z 1) STATUS_DONE))
                   (word.of_Z 0)
        then word.of_Z 1
        else word.of_Z 0) = 0.
  Proof.
    rewrite @word.unsigned_eqb by typeclasses eauto.
    autorewrite with push_unsigned.
    cbv [status_value]. rewrite Z.land_diag.
    destruct_one_match; autorewrite with push_unsigned;
      try congruence; [ ].
    rewrite word_wrap_unsigned in *.
    (* get rid of word.unsigned to match flags_unique_and_nonzero *)
    match goal with H : word.unsigned _ = 0 |- _ =>
                    rewrite <-word.unsigned_of_Z_0 in H;
                      apply word.unsigned_inj in H
    end.
    (* pose the proofs that all the flags are unique and nonzero *)
    pose proof flags_unique_and_nonzero as Hflags.
    cbv [map] in Hflags. simplify_unique_words_in Hflags.
    (* simplify implicit arguments *)
    cbn [width Semantics.word semantics_parameters] in *.
    (* contradiction *)
    congruence.
  Qed.

  Lemma execution_step action args rets t s s':
    execution t s -> step action s args rets s' ->
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s'.
  Proof. intros; cbn [execution]; eauto. Qed.

  Lemma put_wait_get_correct :
    program_logic_goal_for_function! put_wait_get.
  Proof.
    pose proof addrs_unique.

    (* initial processing *)
    repeat straightline.

    (* write input *)
    interaction. repeat straightline.

    (* begin while loop *)
    apply atleastonce_localsmap
      with (v0:=timing.ncycles_processing)
           (lt:=lt)
           (invariant:=
              fun i tr m l =>
                execution tr (BUSY input i)
                /\ map.get l "STATUS_ADDR"%string = Some STATUS_ADDR
                /\ map.get l "VALUE_ADDR"%string = Some VALUE_ADDR
                /\ map.get l "STATUS_DONE"%string = Some STATUS_DONE
                /\ R m).
    { apply lt_wf. }
    { (* case in which the loop breaks immediately (cannot happen) *)
      repeat straightline.
      exfalso. (* proof by contradiction *)

      (* in the loop break case, it must be that the status is DONE (which is
         not the case at the start of the loop) *)
      repeat lazymatch goal with
             | v := word.of_Z 0 |- _ => subst v
             | br := if word.eqb _ (word.of_Z 0) then _ else _ |- _ => subst br
             end.
      rewrite @word.unsigned_eqb in * by typeclasses eauto.
      autorewrite with push_unsigned in *.
      congruence. }
    { (* proof that invariant holds at loop start *)
      ssplit; [ | map_lookup .. | assumption ].
      cbn [execution]. eexists; ssplit; [ eassumption | ].
      match goal with H : write_step _ _ _ _ |- _ => inversion H; subst end.
      eauto with step. }
    { (* invariant holds through loop (or postcondition holds, if loop breaks) *)
      repeat straightline.

      (* get status *)
      interaction. repeat straightline.

      eexists; repeat straightline_with_map_lookup.
      { (* continuation case -- invariant holds *)
        (* find the current measure and handle the case where it's 0 *)
        let i := lazymatch goal with H : execution _ (BUSY _ ?i) |- _ => i end in
        destruct i as [ | i' ].
        { (* i = 0 case *)
          (* contradiction; i=0 guarantees that next status read, but we got a
             non-DONE status *)
          infer. exfalso. eauto using check_done_flag. }
        { (* i = S i' case *)
          exists i'; split; [ | lia ].
          ssplit; [ | map_lookup .. | assumption ].
          cbn [execution]. eexists; ssplit; [ eassumption | ].
          (* break into two possible read cases : DONE and BUSY *)
          match goal with H : read_step _ _ _ _ |- _ => inversion H; subst end;
            try solve [infer]; [ | ].
          { (* BUSY case *)
            econstructor; eauto; [ ].
            infer. econstructor; eauto. }
          { (* DONE case -- contradiction because we already checked that status <> DONE *)
            exfalso. infer. eauto using check_done_flag. } } }
      { (* break case -- postcondition holds *)

        (* get value *)
        interaction. repeat straightline.

        eexists; split; [ map_lookup | ].
        cbv [list_map list_map_body].
        ssplit.
        { eapply execution_step; [ eassumption | ].
          let s := lazymatch goal with |- step _ ?s _ _ _ => s end in
          eapply (ReadStep s); eauto; [ ].
          infer. eauto with step. }
        { eassumption. }
        { infer. reflexivity. } } }
  Qed.
End Proofs.
