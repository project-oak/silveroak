Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import bedrock2.ProgramLogic.
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
  Import parameters.

  Lemma execution_step action args rets t s s':
    execution t s -> step action s args rets s' ->
    execution ((map.empty, action, args, (map.empty, rets)) :: t) s'.
  Proof. intros; cbn [execution]; eauto. Qed.

  Lemma execution_step_read r addr val t s s':
    execution t s -> reg_addr r = addr -> read_step s r val s' ->
    execution ((map.empty, READ, [addr], (map.empty, [val])) :: t) s'.
  Proof.
    intros. eapply execution_step; [ eassumption | ].
    cbv [step]. change (READ =? WRITE)%string with false.
    rewrite String.eqb_refl. eauto.
  Qed.

  Lemma execution_step_write r addr val t s s':
    execution t s -> reg_addr r = addr -> write_step s r val s' ->
    execution ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t) s'.
  Proof.
    intros. eapply execution_step; [ eassumption | ].
    cbv [step]. rewrite String.eqb_refl. eauto.
  Qed.

  Lemma interact_read r call bind addre t m l (post : trace -> mem -> locals -> Prop) addr :
    dexprs m l [addre] [addr] ->
    reg_addr r = addr ->
    (exists s s' val, execution t s /\ read_step s r val s') ->
    (forall s s' val,
        execution t s ->
        read_step s r val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, READ, [addr], (map.empty, [val])) :: t) s' ->
        post ((map.empty, READ, [addr], (map.empty, [val])) :: t)
             m (map.put l bind val)) ->
    cmd call (cmd.interact [bind] READ [addre]) t m l post.
  Proof.
    intros. eapply interact_nomem; [ eassumption | ].
    cbn [Semantics.ext_spec semantics_parameters].
    cbv [ext_spec]. change (READ =? WRITE)%string with false.
    rewrite String.eqb_refl.
    do 2 eexists; ssplit; [ reflexivity || eassumption .. | ].
    intros; ssplit; [ reflexivity | ].
    repeat straightline. eauto using execution_step_read.
  Qed.

  Lemma interact_write r call addre vale t m l
        (post : trace -> mem -> locals -> Prop)  addr val :
    dexprs m l [addre;vale] [addr;val] ->
    reg_addr r = addr ->
    (exists s s', execution t s /\ write_step s r val s') ->
    (forall s s',
        execution t s ->
        write_step s r val s' ->
        (* implied by other preconditions but convenient to have separately *)
        execution ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t) s' ->
        post ((map.empty, WRITE, [addr;val], (map.empty, [])) :: t) m l) ->
    cmd call (cmd.interact [] WRITE [addre; vale]) t m l post.
  Proof.
    intros. eapply interact_nomem; [ eassumption | ].
    cbn [Semantics.ext_spec semantics_parameters].
    cbv [ext_spec]. rewrite String.eqb_refl.
    do 3 eexists; ssplit; [ reflexivity || eassumption .. | ].
    intros; ssplit; [ reflexivity | ].
    repeat straightline. eauto using execution_step_write.
  Qed.
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
    cbv [parameters.read_step]; eauto
  | ];
  repeat straightline.

Ltac interact_write_reg reg :=
  eapply (interact_write reg);
  [ solve_dexprs
  | reflexivity
  | do 2 eexists; ssplit; [ eassumption | ];
    cbv [parameters.write_step]; eauto
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
