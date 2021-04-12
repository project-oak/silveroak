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
  Context {p : parameters} {p_ok : parameters.ok p}.
  Context {consts : constants} {consts_ok : constants.ok consts}.
  Import constants parameters.

  (* plug in implicits *)
  Definition put_wait_get := put_wait_get.

  Instance spec_of_put_wait_get : spec_of put_wait_get :=
    fun function_env =>
      forall tr mem (R : _ -> Prop) input timeout s,
        R mem ->
        execution tr s ->
        word.unsigned timeout <> 0 ->
        let args := [input; timeout] in
        call function_env put_wait_get tr mem args
             (fun tr' mem' rets =>
                (* the trace can be executed *)
                (exists s', execution tr' s')
                (* all the same properties hold on the memory state *)
                /\ R mem'
                /\ exists out success,
                    rets = [out; success]
                    /\ ((* either success = 1 and output matches spec *)
                      (success = word.of_Z 1 /\ out = proc input)
                      (* ... or success = 0 and output is 0 *)
                      \/ (success = word.of_Z 0 /\ out = word.of_Z 0))).

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

  Local Ltac interaction :=
    eapply interact_mmio; [ solve [repeat straightline] | ];
    repeat straightline;
    lazymatch goal with
    | H : step _ _ _ _ _ |- _ => inversion H; clear H; subst
    end.

  Local Ltac subst1_map m :=
    match m with
    | map.put ?m _ _ => subst1_map m
    | ?m => is_var m; subst m
    end.

  Local Ltac map_lookup :=
    repeat lazymatch goal with
           | |- context [map.get ?l] =>
             subst1_map l;
             first [ rewrite map.get_put_diff by congruence
                   | apply map.get_put_same ]
           end.
  (* if these aren't opaque, initial call to straightline computes them *)
  Opaque STATUS_ADDR VALUE_ADDR STATUS_IDLE STATUS_BUSY STATUS_DONE.

  Hint Extern 4 (step _ ?s _ _ _) => eapply (ReadStep s) : step.
  Hint Extern 4 (step _ ?s _ _ _) => eapply (WriteStep s) : step.
  Hint Constructors reg_addr : step.

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
           | H : execution _ (DONE _) |- _ => invert_nobranch H; destruct_products
           | H : step _ _ _ _ (DONE _) |- _ => invert_nobranch H
           | H1 : execution ?t _, H2 : execution ?t _ |- _ =>
             pose proof execution_unique _ _ _ H1 H2; subst;
             clear H2; one_goal_or_solved ltac:(try congruence)
           end.

  Lemma put_wait_get_correct :
    program_logic_goal_for_function! put_wait_get.
  Proof.
    pose proof addrs_unique.

    (* initial processing *)
    repeat straightline.

    (* read status *)
    interaction. repeat straightline.

    (* handle branch *)
    unfold1_cmd_goal. cbv [cmd_body].
    repeat straightline.
    split; repeat straightline.
    2:{
      (* first handle the easy case where STATUS <> IDLE *)
      (* done; prove postcondition *)
      cbv [list_map list_map_body].
      repeat straightline.
      cbn [execution].
      ssplit; eauto with step; [ ].
      do 2 eexists; ssplit; [ reflexivity | ].
      right; ssplit; reflexivity. }

    (* write input *)
    interaction. repeat straightline.

    (* begin while loop *)
    apply atleastonce_localsmap
      with (v2:=word.unsigned timeout)
           (lt:=fun n m => 0 <= n < m)
           (invariant:=
              fun i tr m l =>
                execution tr (BUSY input)
                /\ R m
                /\ 0 < i < 2 ^ width
                /\ map.get l "out"%string = Some (word.of_Z 0)
                /\ map.get l "success"%string = Some (word.of_Z 0)
                /\ map.get l "timeout"%string = Some (word.of_Z i)).
    1:apply Z.lt_wf.
    all:cbv [Markers.split].
    { (* case where timeout = 0; loop break *)
      exists timeout.
      ssplit; repeat straightline.
      cbv [list_map list_map_body].
      repeat straightline.
      cbn [execution].
      ssplit; eauto with step; [ ].
      do 2 eexists; ssplit; [ reflexivity | ].
      right; ssplit; reflexivity. }
    { (* invariant holds at start of loop *)
      pose proof (word.unsigned_range timeout).
      ssplit; [ | assumption
                | lia
                | lia
                | map_lookup
                | map_lookup
                | rewrite word.of_Z_unsigned; map_lookup ].
      eexists; ssplit; eauto with step.
      lazymatch goal with
      | H : write_step _ _ _ _ |- _ =>
        inversion H; subst
      end.
      eauto with step. }
    { (* invariant holds through loop (or postcondition holds, if loop breaks) *)
      repeat straightline.

      (* get status *)
      interaction. repeat straightline.

      (* branch on whether status is DONE *)
      unfold1_cmd_goal. cbv [cmd_body].
      repeat straightline.
      eexists; ssplit.
      { (* get value of status (straightline should handle this, but assumes
           word is not abstract) *)
        repeat straightline.
        eexists; split; repeat straightline.
        map_lookup. }
      { (* case where status is DONE *)
        repeat straightline.
        interaction. repeat straightline.
        eexists; ssplit; repeat straightline.
        { eexists; ssplit; eauto.
          map_lookup. }
        { (* continuation case is irrelevant here; the timeout was reset to 0,
             so break *)
          match goal with
          | H : word.unsigned ?v <> 0 |- _ =>
            change v with (word.of_Z 0) in H;
            rewrite word.unsigned_of_Z_0 in H;
            contradiction H; trivial
          end. }
        { (* break case; prove postcondition holds *)
          eexists.
          split; repeat straightline; [ map_lookup | ].
          cbv [list_map list_map_body].
          eexists; repeat straightline; ssplit; eauto.
          { map_lookup. }
          { do 2 eexists.
            split; eauto with step. }
          { do 2 eexists; ssplit; [ reflexivity | ].
            left; ssplit; try reflexivity.

            infer. } } }
      { (* case where status != DONE *)
        repeat straightline.

        (* timeout = timeout - 1 (annoying because straightline assumes it can
           compute maps *)
        eexists; ssplit; repeat straightline.
        { eexists; ssplit; repeat straightline.
          map_lookup. eassumption. }
        eexists; ssplit; repeat straightline.
        { eexists; ssplit; repeat straightline.
          map_lookup. }
        { (* continuation case; prove the invariant holds *)
          lazymatch goal with
          | |- exists ctr', _ /\ (0 <= ctr' < ?ctr) =>
            let c' := constr:(word.sub (word.of_Z ctr) (word.of_Z 1)) in
            (exists (word.unsigned c'));
            set (i:=ctr) in *;
            assert (0 <= word.unsigned c' < i)
          end.
          { (* annoying modulo proof; prove that even with word-truncation,
               0 <= i-1 < i *)
            rewrite word.unsigned_sub in *.
            rewrite word.unsigned_of_Z_1, word.unsigned_of_Z in *.
            cbv [word.wrap] in *. pose proof word.modulus_pos.
            rewrite (Z.mod_small i) in * by lia.
            rewrite (Z.mod_small (i - 1)) in * by lia.
            lia. }
          subst i.
          ssplit; [ | assumption
                    | lia
                    | lia
                    | map_lookup; assumption
                    | map_lookup; assumption
                    | rewrite word.of_Z_unsigned; map_lookup
                    | lia
                    | lia ].
          cbn [execution].
          eexists; ssplit; eauto.
          econstructor; eauto.
          infer.
          let H := lazymatch goal with H : read_step ?s ?r ?v _
                                       |- read_step ?s ?r ?v _ => H end in
          inversion H; clear H; subst; [ constructor; reflexivity | ].
          (* contradiction case in which the status read was DONE (we have
             already checked that it wasn't) *)
          (* pose the proofs that all the flags are unique and nonzero *)
          pose proof flags_unique_and_nonzero as Hflags.
          cbv [map] in Hflags.
          simplify_unique_words_in Hflags.
          cbv [status_value] in *.
          lazymatch goal with
          | H : word.unsigned (word.and ?x ?y) = 0 |- _ =>
            unify x y; (* x = y; this is a contradiction *)
              rewrite word.unsigned_and, Z.land_diag in H;
              rewrite word_wrap_unsigned in H;
              rewrite <-word.unsigned_of_Z_0 in H;
              apply word.unsigned_inj in H
          end.
          (* simplify implicit arguments *)
          cbn [width Semantics.word semantics_parameters] in *.
          congruence. }
        { (* break case -- timeout exceeded *)
          eexists.
          split; repeat straightline; [ map_lookup; eassumption | ].
          cbv [list_map list_map_body].
          eexists; repeat straightline; ssplit; eauto.
          { map_lookup; eassumption. }
          { do 2 eexists.
            split; eauto with step. }
          { do 2 eexists; ssplit; [ reflexivity | ].
            right; ssplit; reflexivity. } } } }
  Qed.
End Proofs.
