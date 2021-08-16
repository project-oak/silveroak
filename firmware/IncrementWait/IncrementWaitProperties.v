Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.Loops.
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
Require Import Bedrock2Experiments.ProgramSemantics32.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.StateMachineProperties.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.IncrementWait.IncrementWait.
Import Syntax.Coercions List.ListNotations.
Local Open Scope Z_scope.

Section Proofs.
  Context {word: word.word 32} {word_ok: word.ok word}
          {mem: map.map word Byte.byte} {mem_ok: Interface.map.ok mem}
          {circuit_spec : circuit_behavior}.

  Global Instance spec_of_put_wait_get : spec_of "put_wait_get" :=
    fun function_env =>
      forall (tr : trace) (m : mem) (R : _ -> Prop) input,
        (* no special requirements of the memory *)
        R m ->
        (* circuit must start in IDLE state *)
        execution (M := increment_wait_state_machine) tr IDLE ->
        let args := [input] in
        call function_env put_wait_get tr m args
             (fun tr' m' rets =>
                (* the circuit is back in IDLE state *)
                execution (M := increment_wait_state_machine) tr' IDLE
                (* ...and the same properties as before hold on the memory *)
                /\ R m'
                (* ...and output matches spec *)
                /\ rets = [proc input]).

  Lemma execution_unique (t : trace) s1 s2 :
    execution t s1 ->
    execution t s2 ->
    s1 = s2.
  Proof.
    eapply StateMachineProperties.execution_unique; intros.
    all:repeat match goal with
           | |- _ => contradiction
           | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
           | |- ?x = ?x => reflexivity
           | |- _ => destruct_one_match_hyp
           | |- _ => progress logical_simplify; subst
           | |- _ => congruence
           | |- _ => progress cbv [read_step state_machine.read_step
                                   write_step state_machine.write_step state_machine.reg_addr
                                   increment_wait_state_machine] in *
           | H: reg_addr _ = reg_addr _ |- _ => eapply reg_addrs_unique in H
           | |- _ => progress cbv [reg_addr status_value] in *
           | H : _ \/ _ |- _ => destruct H
           end.
    all: match goal with
         | H: word.slu _ _ = word.slu _ _ |- _ => apply (f_equal word.unsigned) in H; rename H into A
         end.
    all: rewrite !word.unsigned_slu_shamtZ in A by (cbv; intuition congruence).
    all: unfold word.wrap in *; rewrite word.unsigned_of_Z_nowrap in A by (cbv; intuition congruence).
    all: discriminate A.
  Qed.

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
    word.eqb (word.and (status_value STATUS_DONE)
                       (word.slu (word.of_Z 1) (word.of_Z STATUS_DONE)))
             (word.of_Z 0) = false.
  Proof.
    cbv [status_value STATUS_DONE]. rewrite word.unsigned_eqb.
    push_unsigned. rewrite Z.land_diag.
    apply Z.eqb_neq; intro Heq.
    discriminate Heq.
  Qed.

  Lemma word_and_shiftl_1_diff n m :
    word.unsigned n < 32 ->
    word.unsigned m < 32 ->
    word.slu (word.of_Z 1) n <> word.slu (word.of_Z (word:=word) 1) m ->
    word.and (word.slu (word.of_Z 1) n) (word.slu (word.of_Z 1) m) = word.of_Z 0.
  Proof.
    pose proof word.width_pos.
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

  Lemma check_done_flag_busy :
    word.and (status_value STATUS_BUSY)
             (word.slu (word.of_Z 1) (word.of_Z STATUS_DONE)) = word.of_Z 0.
  Proof.
    cbv [STATUS_BUSY STATUS_DONE].
    apply word_and_shiftl_1_diff; try intro; push_unsigned; try reflexivity.
    eapply (f_equal word.unsigned) in H.
    rewrite !word.unsigned_slu in H.
    2-3: rewrite word.unsigned_of_Z_nowrap; cbv; intuition congruence.
    rewrite !word.unsigned_of_Z_nowrap in H by (cbv; intuition congruence).
    discriminate H.
  Qed.

  Lemma check_done_flag :
    word.unsigned
      (word:=word)
      (if
          word.eqb (word.and (status_value STATUS_DONE)
                             (word.slu (word.of_Z 1) (word.of_Z STATUS_DONE)))
                   (word.of_Z 0)
        then word.of_Z 1
        else word.of_Z 0) = 0.
  Proof.
    rewrite @word.unsigned_eqb by typeclasses eauto.
    cbv [status_value STATUS_DONE].
    push_unsigned.
    rewrite Z.land_diag.
    reflexivity.
  Qed.

  Local Ltac interact_read_reg reg :=
    eapply (interact_read (M := increment_wait_state_machine) 4 reg);
    [ repeat straightline_with_map_lookup; reflexivity
    | reflexivity
    | do 3 eexists; split; [ eassumption | ];
      cbv [read_step state_machine.read_step increment_wait_state_machine]; eauto
    | ];
    repeat straightline.

  Local Ltac interact_write_reg reg :=
    eapply (interact_write (M := increment_wait_state_machine) 4 reg);
    [ repeat straightline_with_map_lookup; reflexivity
    | reflexivity
    | do 2 eexists; ssplit; [ eassumption | ];
      cbv [write_step state_machine.write_step increment_wait_state_machine]; eauto
    | ];
    repeat straightline.

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

    (* write input *)
    interact_write_reg VALUE.

    (* simplify post-write guarantees *)
    cbv [state_machine.write_step increment_wait_state_machine write_step] in *.
    repeat straightline.
    repeat (destruct_one_match_hyp; try contradiction).
    subst.

    (* begin while loop *)
    apply atleastonce_localsmap
      with (v0:=ncycles_processing)
           (lt:=lt)
           (invariant:=
              fun i tr m l =>
                execution (M := increment_wait_state_machine) tr (BUSY input i) /\ R m).
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
      cbn [execution]. eauto. }
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

        cbv [state_machine.read_step increment_wait_state_machine read_step] in *. straightline.
        (* break into two possible read cases : DONE and BUSY *)
        lazymatch goal with H : _ \/ _ |- _ => destruct H end;
          logical_simplify; subst.
        { (* DONE case; contradiction *)
          exfalso; infer.
          pose proof check_done_flag_done as Hflag.
          unfold STATUS_DONE in *.
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
        cbv [read_step state_machine.read_step increment_wait_state_machine]. split; [reflexivity|].
        right; eauto. }
      { (* break case -- postcondition holds *)

        (* break into two possible read cases : DONE and BUSY *)
        cbv [state_machine.read_step increment_wait_state_machine read_step] in *. straightline.
        lazymatch goal with H : _ \/ _ |- _ => destruct H end;
          logical_simplify; subst.
        2:{ (* BUSY case; contradiction *)
          exfalso; infer.
          unfold STATUS_BUSY in *.
          lazymatch goal with H : word.unsigned (if _ then _ else _) = 0 |- _ =>
                          erewrite word.eqb_eq in H by apply check_done_flag_busy;
                            autorewrite with push_unsigned in H
          end.
          congruence. }

        (* get value *)
        interact_read_reg VALUE. repeat straightline.

        (* simplify post-read guarantees *)
        infer. cbv [read_step state_machine.read_step increment_wait_state_machine] in *. repeat straightline.
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

End Proofs.
