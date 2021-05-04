Require Import Coq.Lists.List.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.Tactics.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.WordProperties.
Require Import Cava.Util.Tactics.
Import ListNotations.
Local Open Scope Z_scope.

Section Proofs.
  Context {width word} {p : StateMachineSemantics.parameters width word}
          {p_ok : parameters.ok p}.

  Lemma execution_step action args rets t s s':
    execution t s -> step action s args rets s' ->
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s'.
  Proof. intros; cbn [execution]; eauto. Qed.

  Lemma invert1_execution action args rets t s':
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s' ->
    exists s, execution t s /\ step action s args rets s'.
  Proof. intros; cbn [execution]; eauto. Qed.

  Lemma invert1_step action args rets s s':
    step action s args rets s' ->
    (exists r addr val,
        args = [addr]
        /\ rets = [val]
        /\ parameters.reg_addr r = addr
        /\ parameters.read_step s r val s')
    \/ (exists r addr val,
        args = [addr; val]
        /\ rets = []
        /\ parameters.reg_addr r = addr
        /\ parameters.write_step s r val s').
  Proof.
    inversion 1; subst; [ left | right ];
      do 3 eexists; ssplit; try reflexivity;
        assumption.
  Qed.


  Lemma invert1_step_read addr rets s s':
    step parameters.READ s [addr] rets s' ->
    (exists r val,
        parameters.reg_addr r = addr
        /\ rets = [val]
        /\ parameters.read_step s r val s').
  Proof. inversion 1; subst. eexists; eauto. Qed.

  Lemma invert1_step_write addr val rets s s':
    step parameters.WRITE s [addr; val] rets s' ->
    (exists r,
        parameters.reg_addr r = addr
        /\ rets = []
        /\ parameters.write_step s r val s').
  Proof. inversion 1; subst. eexists; eauto. Qed.

  Lemma interact_mmio call action binds arges t m l
        (post : trace -> mem -> locals -> Prop) (args : list Semantics.word) :
    dexprs m l arges args ->
    (forall s' (rets : list Semantics.word),
        execution ((map.empty, action, args, (map.empty, rets)) :: t) s' ->
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
End Proofs.

(**** Tactics for state machine proofs ****)

Ltac invert_step :=
  lazymatch goal with
  | H : step _ _ _ _ _ |- _ =>
    first [ apply @invert1_step_read in H; destruct H as [? [? [? [? ?]]]]
          | apply @invert1_step_write in H; destruct H as [? [? [? ?]]]
          | inversion H; clear H ]; subst;
    repeat lazymatch goal with
           | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst end
  end.

(* shorthand for applying [interact_mmio] and then doing some simplification
   afterwards; takes a tactic argument which is run on the [dexprs] side
   condition generated by interact_mmio *)
Ltac interaction tac :=
  (* get trace *)
  let t := lazymatch goal with
           | |- cmd _ (cmd.interact _ _ _) ?t _ _ _ => t end in
  eapply interact_mmio; [ tac | ]; intros;
  lazymatch goal with
  | H : execution (_ :: t) _ |- _ =>
    pose proof H; apply invert1_execution in H; destruct H as [? [? ?]]
  end; invert_step.

(* Remove [execution] hypotheses that are superceded by later ones; improves
   proof performance *)
(* Warning: be careful not to remove useful information with this tactic! *)
Ltac clear_old_executions :=
  repeat lazymatch goal with
         | H1 : execution ?t _, H2 : execution (_ :: ?t) _ |- _ =>
           clear H1
         end.