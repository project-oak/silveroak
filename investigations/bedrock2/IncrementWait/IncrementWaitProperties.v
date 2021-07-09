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
Require Import coqutil.Z.bitblast.
Require Import Cava.Util.Tactics.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Import Syntax.Coercions List.ListNotations.
Local Open Scope Z_scope.

Section Proofs.
  Context {p : parameters} {p_ok : parameters.ok p}
          {circuit_spec : circuit_behavior}.
  Import parameters.

  Global Instance spec_of_put_wait_get : spec_of "put_wait_get" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) input,
        (* no special requirements of the memory *)
        R m ->
        (* circuit must start in IDLE state *)
        execution (p := state_machine_parameters) tr IDLE ->
        let args := [input] in
        call function_env put_wait_get tr m args
             (fun tr' m' rets =>
                (* the circuit is back in IDLE state *)
                execution (p := state_machine_parameters) tr' IDLE
                (* ...and the same properties as before hold on the memory *)
                /\ R m'
                (* ...and output matches spec *)
                /\ rets = [proc input]).

  Local Ltac simplify_implicits :=
    change Semantics.word with parameters.word in *;
    change Semantics.mem with parameters.mem in *;
    change Semantics.width with 32 in *.

  Lemma execution_unique (t : trace) s1 s2 :
    execution (p := state_machine_parameters) t s1 ->
    execution (p := state_machine_parameters) t s2 ->
    s1 = s2.
  Proof.
    revert s1 s2.
    induction t; cbn [execution]; [ congruence | ].
    intros; destruct_products.
    match goal with
    | H1 : execution t ?s1, H2 : execution t ?s2 |- _ =>
      specialize (IHt _ _ H1 H2); subst
    end.
    cbv [step] in *.
    repeat first [ destruct_one_match_hyp; try contradiction
                 | progress logical_simplify; subst
                 | congruence ].
    { cbv [write_step] in *.
      repeat first [ destruct_one_match_hyp; try contradiction
                   | progress logical_simplify; subst
                   | congruence ]. (*}
    { cbv [read_step] in *.
      repeat lazymatch goal with
             | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
             | H : _ \/ _ |- _ => destruct H
             | |- ?x = ?x => reflexivity
             | _ => first  [ destruct_one_match_hyp; try contradiction
                          | progress logical_simplify; subst
                          | cbv [reg_addr status_value] in *;
                            simplify_implicits; congruence ]
             end. *)
  Admitted.

  Local Ltac infer :=
    repeat match goal with
           | H1 : execution ?t _, H2 : execution ?t _ |- _ =>
             pose proof execution_unique _ _ _ H1 H2; subst;
             clear H2; one_goal_or_solved ltac:(try congruence)
           | H : BUSY _ _ = BUSY _ _ |- _ => invert_nobranch H
           | H : ?x = ?x |- _ => clear H
           end.

  (* (status value STATUS_DONE) & (1 << STATUS_DONE) != 0 *)
  Lemma check_done_flag_done :
    word.eqb (word.and (status_value (word.of_Z 31))
                       (word.slu (word.of_Z 1) (word.of_Z 31)))
             (word.of_Z 0) = false.
  Proof.
    (* pose the proofs that all the flags are unique and nonzero
    pose proof status_flags_unique_and_nonzero as Hflags.
    cbv [map] in Hflags. simplify_unique_words_in Hflags.
    cbv [status_value]. rewrite word.unsigned_eqb.
    push_unsigned. rewrite Z.land_diag.
    apply Z.eqb_neq; intro Heq.
    rewrite <-word.unsigned_of_Z_0 in Heq.
    apply word.unsigned_inj in Heq.
    simplify_implicits.
    congruence.
  Qed. *)
  Admitted.

  Lemma word_and_shiftl_1_diff n m :
    word.unsigned n < width ->
    word.unsigned m < width ->
    word.slu (word.of_Z 1) n <> word.slu (word.of_Z (word:=word) 1) m ->
    word.and (word.slu (word.of_Z 1) n) (word.slu (word.of_Z 1) m) = word.of_Z 0.
  Proof.
    pose proof word.width_pos. simplify_implicits.
    intros. apply word.unsigned_inj. push_unsigned.
    cbv [word.wrap]. rewrite <-Z.land_ones by lia.
    Z.bitblast.
    rewrite !Z_testbit_1_l.
    repeat lazymatch goal with
           | |- context [(?x =? 0)] => destr (x =? 0)
           end; try reflexivity.
    subst. exfalso.
    assert (word.unsigned n = word.unsigned m) as Heq by lia.
    apply word.unsigned_inj in Heq; subst. congruence.
  Qed.

  (*
  Lemma check_done_flag_busy :
    word.and (status_value STATUS_BUSY)
             (word.slu (word.of_Z 1) STATUS_DONE) = word.of_Z 0.
  Proof.
    (* pose the proofs that all the flags are unique and nonzero *)
    pose proof status_flags_unique_and_nonzero as Hflags.
    cbv [map] in Hflags. simplify_unique_words_in Hflags.
    (* pose proof that flags are all < width *)
    pose proof flags_lt_width.
    repeat lazymatch goal with
           | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
           | H : Forall _ [] |- _ => clear H
           end.
    apply word_and_shiftl_1_diff; auto.
  Qed.
  *)

  Lemma check_done_flag :
    word.unsigned
      (word:=word)
      (if
          word.eqb (word.and (status_value (word.of_Z 31))
                             (word.slu (word.of_Z 1) (word.of_Z 31)))
                   (word.of_Z 0)
        then word.of_Z 1
        else word.of_Z 0) = 0.
  Proof.
    rewrite @word.unsigned_eqb by typeclasses eauto.
    autorewrite with push_unsigned.
    cbv [status_value]. rewrite Z.land_diag.
    destruct_one_match; push_unsigned; try congruence; [ ].
    (* get rid of word.unsigned to match flags_unique_and_nonzero *)
    match goal with H : word.unsigned _ = 0 |- _ =>
                    rewrite <-word.unsigned_of_Z_0 in H;
                      apply word.unsigned_inj in H
    end.
    (* pose the proofs that all the flags are unique and nonzero
    pose proof status_flags_unique_and_nonzero as Hflags.
    cbv [map] in Hflags. simplify_unique_words_in Hflags.
    (* simplify implicit arguments *)
    cbn [width Semantics.word semantics_parameters] in *.
    (* contradiction *)
    congruence.
  Qed. *)
  Admitted.

(*
  Local Ltac interact_read_reg reg :=
    eapply (interact_read reg);
    [ repeat straightline_with_map_lookup; reflexivity
    | reflexivity
    | do 3 eexists; split; [ eassumption | ];
      cbv [read_step]; eauto
    | ];
    repeat straightline.

  Local Ltac interact_write_reg reg :=
    eapply (interact_write reg);
    [ repeat straightline_with_map_lookup; reflexivity
    | reflexivity
    | do 2 eexists; ssplit; [ eassumption | ]; cbv [write_step]; eauto
    | ];
    repeat straightline.
*)

  Hint Rewrite @map.get_put_same using typeclasses eauto : mapsimpl.
  Hint Rewrite @map.get_put_diff using (typeclasses eauto || congruence) : mapsimpl.
  Ltac map_lookup_subst target :=
    lazymatch goal with
    | |- map.get ?m ?k = _ =>
      lazymatch m with
      | context [target] => idtac
      | _ => subst1_map m; map_lookup_subst target
      end
    end.
  Ltac map_lookup ::=
    lazymatch goal with
    | |- map.get ?m ?k = Some _ =>
      autorewrite with mapsimpl;
      lazymatch goal with
      | |- Some _ = Some _ => reflexivity
      | H : map.get m k = Some _ |- _ => apply H
      | H : map.get ?m2 k = Some _ |- _ =>
        map_lookup_subst m2;
        autorewrite with mapsimpl; apply H
      | m2 := context [map.put _ k _] |- _ =>
        map_lookup_subst m2;
        autorewrite with mapsimpl; reflexivity
      end
    end.

  Lemma put_wait_get_correct :
    program_logic_goal_for_function! put_wait_get.
  Proof.
    (* initial processing *)
    repeat straightline.
  Admitted.
  (*
    (* write input *)
    interact_write_reg VALUE. repeat straightline.

    (* simplify post-write guarantees *)
    cbv [write_step] in *.
    repeat (destruct_one_match_hyp; try contradiction).
    subst.

    (* begin while loop *)
    apply atleastonce_localsmap
      with (v0:=ncycles_processing)
           (lt:=lt)
           (invariant:=
              fun i tr m l =>
                execution tr (BUSY input i) /\ R m).
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
      rewrite Z.land_0_l, Z.eqb_refl in *.
      congruence. }
    { (* proof that invariant holds at loop start *)
      ssplit; [ | map_lookup .. | assumption ].
      cbn [execution]. eexists; ssplit; [ eassumption | ].
      cbv [step write_step]. rewrite String.eqb_refl.
      exists VALUE; ssplit; eauto. }
    { (* invariant holds through loop (or postcondition holds, if loop breaks) *)
      repeat straightline.

      (* get status *)
      interact_read_reg STATUS. repeat straightline.

      (* simplify post-read guarantees *)
      infer. cbv [read_step] in *.
      repeat (destruct_one_match_hyp; try contradiction).
      subst.

      eexists; repeat straightline_with_map_lookup.
      { (* continuation case -- invariant holds *)

        match goal with H : _ |- _ => apply word.if_nonzero, word.eqb_true in H end.

        (* break into two possible read cases : DONE and BUSY *)
        lazymatch goal with H : _ \/ _ |- _ => destruct H end;
          logical_simplify; subst.
        { (* DONE case; contradiction *)
          exfalso; infer.
          pose proof check_done_flag_done as Hflag.
          simplify_implicits.
          match goal with H : word.and _ _ = word.of_Z 0 |- _ =>
                          rewrite H in Hflag end.
          apply word.eqb_false in Hflag. congruence. }

        (* new measure *)
        cbv [Markers.split].
        lazymatch goal with
        | |- exists v', _ /\ (v' < S ?v)%nat => exists v; split; [ | lia ]
        end.

        ssplit; [ | map_lookup .. | assumption ].
        eapply execution_step_read with (r:=STATUS); [ eassumption | reflexivity | ].
        cbv [read_step]. right; eauto. }
      { (* break case -- postcondition holds *)

        (* break into two possible read cases : DONE and BUSY *)
        lazymatch goal with H : _ \/ _ |- _ => destruct H end;
          logical_simplify; subst.
        2:{ (* BUSY case; contradiction *)
          exfalso; infer. simplify_implicits.
          match goal with H : word.unsigned (if _ then _ else _) = 0 |- _ =>
                          erewrite word.eqb_eq in H by apply check_done_flag_busy;
                            autorewrite with push_unsigned in H
          end.
          congruence. }

        (* get value *)
        interact_read_reg VALUE. repeat straightline.

        (* simplify post-read guarantees *)
        infer. cbv [read_step] in *.
        repeat (destruct_one_match_hyp; try contradiction);
          try lazymatch goal with
              | H : word.unsigned (word.of_Z 1) = 0 |- _ =>
                rewrite word.unsigned_of_Z_1 in H; congruence
              end.
        logical_simplify; subst.

        eexists; split; [ map_lookup | ].
        cbv [list_map list_map_body].
        ssplit; eauto. } }
  Qed.
  *)
End Proofs.
