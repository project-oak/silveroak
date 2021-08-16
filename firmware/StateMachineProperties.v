Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import Bedrock2Experiments.LibBase.MMIOLabels.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Cava.Util.Tactics.
Import ListNotations.
Local Open Scope Z_scope.

Section Proofs.
  Context {word: word.word 32} {mem: map.map word Byte.byte} {locals: map.map string word}
          {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok: map.ok locals}
          {M : state_machine.parameters} {M_ok : state_machine.ok M}.
  Import state_machine.

  Lemma execution_step action args rets t s s':
    execution t s -> step action s args rets s' ->
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s'.
  Proof using . intros; cbn [execution]; eauto. Qed.

  Lemma execution_step_read r addr val t sz s s':
    execution t s -> reg_addr r = addr -> read_step sz s r val s' ->
    execution ((map.empty, access_size_to_MMIO_read sz, [addr], (map.empty, [val])) :: t) s'.
  Proof using .
    intros. eapply execution_step; [ eassumption | ].
    cbv [step].
    change (if _: bool then False else ?x) with x.
    unfold access_size_to_MMIO_read at 1.
    destruct (natToStr (sz * 8)); change (if _: bool then ?x else False) with x; eauto 10.
  Qed.

  Lemma execution_step_write r addr val t sz s s':
    execution t s -> reg_addr r = addr -> write_step sz s r val s' ->
    execution ((map.empty, access_size_to_MMIO_write sz, [addr;val], (map.empty, [])) :: t) s'.
  Proof using .
    intros. eapply execution_step; [ eassumption | ].
    cbv [step].
    unfold access_size_to_MMIO_write at 1.
    destruct (natToStr (sz * 8)); change (if _: bool then ?x else _) with x; eauto 10.
  Qed.

  Lemma interact_read sz r call bind addre t m l (post : trace -> mem -> locals -> Prop) addr :
    dexprs m l [addre] [addr] ->
    reg_addr r = addr ->
    (exists s s' val, execution t s /\ read_step sz s r val s') ->
    (forall s s' val,
        execution t s ->
        read_step sz s r val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, access_size_to_MMIO_read sz, [addr], (map.empty, [val])) :: t) s' ->
        post ((map.empty, access_size_to_MMIO_read sz, [addr], (map.empty, [val])) :: t)
             m (map.put l bind val)) ->
    cmd call (cmd.interact [bind] (access_size_to_MMIO_read sz) [addre]) t m l post.
  Proof using word_ok mem_ok M_ok.
    intros. eapply interact_nomem; [ eassumption | ].
    cbv [ext_spec].
    change (if _: bool then _ else ?x) with x.
    unfold access_size_to_MMIO_read at 1.
    destruct (natToStr (sz * 8)); change (if _: bool then ?x else False) with x;
      repeat match goal with
             | |- _ => straightline
             | |- exists _, _ => eexists
             | |- _ => eassumption
             | |- _ /\ _ => split
             | |- _ => solve [eauto using execution_step_read]
             end.
  Qed.

  Lemma interact_write sz r call addre vale t m l
        (post : trace -> mem -> locals -> Prop)  addr val :
    dexprs m l [addre;vale] [addr;val] ->
    reg_addr r = addr ->
    (exists s s', execution t s /\ write_step sz s r val s') ->
    (forall s s',
        execution t s ->
        write_step sz s r val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, access_size_to_MMIO_write sz, [addr;val], (map.empty, [])) :: t) s' ->
        post ((map.empty, access_size_to_MMIO_write sz, [addr;val], (map.empty, [])) :: t) m l) ->
    cmd call (cmd.interact [] (access_size_to_MMIO_write sz) [addre; vale]) t m l post.
  Proof using word_ok mem_ok M_ok.
    intros. eapply interact_nomem; [ eassumption | ].
    cbv [ext_spec].
    unfold access_size_to_MMIO_write at 1.
    destruct (natToStr (sz * 8)); change (if _: bool then ?x else _) with x;
      repeat match goal with
             | |- _ => straightline
             | |- exists _, _ => eexists
             | |- _ => eassumption
             | |- _ /\ _ => split
             | |- _ => solve [eauto using execution_step_write]
             end.
  Qed.

  Section Uniqueness.
    (* These hypotheses disallow internal nondeterminism (ie nondeterminism that does
       not show up in the trace), but still allows external nondeterminism. *)
    Hypothesis initial_state_unique: forall s s',
      is_initial_state s -> is_initial_state s' -> s = s'.
    Hypothesis read_step_unique: forall n r v s s' s'',
      read_step n r v s s' ->
      read_step n r v s s'' ->
      s' = s''.
    Hypothesis write_step_unique: forall n r v s s' s'',
      write_step n r v s s' ->
      write_step n r v s s'' ->
      s' = s''.

    Lemma step_unique: forall a prevH args rets s s',
      step a prevH args rets s ->
      step a prevH args rets s' ->
      s = s'.
    Proof.
      unfold step. intros.
      destruct (String.prefix MMIOLabels.WRITE_PREFIX a).
      - simp.
        replace sz0 with sz in *. 2: {
          pose proof (write_step_size_valid _ _ _ _ _ Hp3) as V1. simpl in V1.
          pose proof (write_step_size_valid _ _ _ _ _ H0p1) as V2. simpl in V2.
          destruct V1 as [? | [? | [? | ?]]]; destruct V2 as [? | [? | [? | ?]]]; subst;
            reflexivity || discriminate || contradiction.
        }
        eapply reg_addr_unique in Hp0. subst r1.
        eapply write_step_unique; eassumption.
      - destruct (String.prefix MMIOLabels.READ_PREFIX a). 2: contradiction. simp.
        replace sz0 with sz in *. 2: {
          pose proof (read_step_size_valid _ _ _ _ _ Hp3) as V1. simpl in V1.
          pose proof (read_step_size_valid _ _ _ _ _ H0p1) as V2. simpl in V2.
          destruct V1 as [? | [? | [? | ?]]]; destruct V2 as [? | [? | [? | ?]]]; subst;
            reflexivity || discriminate || contradiction.
        }
        eapply reg_addr_unique in Hp0. subst r0.
        eapply read_step_unique; eassumption.
    Qed.

    Lemma execution_unique: forall t s s',
        execution t s -> execution t s' -> s = s'.
    Proof.
      induction t; cbn [execution]; intros.
      - eauto using initial_state_unique.
      - destruct a as (((mGive & a) & args) & (mReceive & rets)).
        destruct H as (prev & E & St). destruct H0 as (prev' & E' & St').
        specialize (IHt _ _ E E'). subst prev'.
        eapply step_unique; eassumption.
    Qed.
  End Uniqueness.
End Proofs.

(**** Tactics for state machine proofs ****)

Ltac solve_dexprs :=
  fail "Redefine the solve_dexprs tactic, and the new definition will be applied
  to the dexprs side condition of interact_read and interact_write!".

Ltac interact_read_reg reg :=
  eapply (interact_read reg);
  [ solve_dexprs
  | reflexivity
  | do 3 eexists; split; [ eassumption | ];
    cbv [state_machine.read_step]; eauto
  | ];
  repeat straightline.

Ltac interact_write_reg reg :=
  eapply (interact_write reg);
  [ solve_dexprs
  | reflexivity
  | do 2 eexists; ssplit; [ eassumption | ];
    cbv [state_machine.write_step]; eauto
  | ];
  repeat straightline.

(* Remove [execution] hypotheses that are superceded by later ones; improves
   proof performance *)
(* Warning: be careful not to remove useful information with this tactic! *)
Ltac clear_old_executions :=
  repeat lazymatch goal with
         | H1 : execution ?t _, H2 : execution (_ :: ?t) _ |- _ =>
           clear H1
         end.
