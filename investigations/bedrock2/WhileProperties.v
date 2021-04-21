Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Local Open Scope Z_scope.

(* Proofs about cmd.while *)

Section Proofs.
  Context {p : Semantics.parameters} {p_pk : Semantics.parameters_ok p}.

  Fixpoint repeat_logic_step
           (logic : trace -> mem -> locals ->
                    (trace -> mem -> locals -> Prop) -> Prop)
           (n : nat) post : trace -> mem -> locals -> Prop :=
    match n with
    | O => post
    | S n => fun t m l => logic t m l (repeat_logic_step logic n post)
    end.

  Lemma unroll_while functions conde body t m l
        (iterations : nat)
        (post : trace -> mem -> locals -> Prop) (cond : Semantics.word) :
    repeat_logic_step
      (fun t m l post =>
         exists cond,
           dexpr m l conde cond
           /\ word.unsigned cond <> 0
           /\ cmd (call functions) body t m l post)
      iterations (fun t m l =>
                    dexpr m l conde cond
                    /\ word.unsigned cond = 0
                    /\ post t m l) t m l ->
    cmd (call functions) (cmd.while conde body) t m l post.
  Proof.
    lazymatch goal with
      |- repeat_logic_step ?logic _ ?post _ _ _ -> _ =>
      set (step:=logic);
        set (P:=post)
    end.
    intros. exists nat, lt, (fun i => repeat_logic_step step i P).
    ssplit.
    { exact lt_wf. }
    { eauto. }
    { intro i. destruct i; cbn [repeat_logic_step].
      { (* i=0 case (contradiction) *)
        subst P. repeat straightline.
        eexists; ssplit; eauto; congruence. }
      { (* i <> 0 case *)
        subst step. repeat straightline.
        eexists; ssplit; eauto; try congruence; [ ].
        repeat straightline.
        eapply Proper_cmd; [ apply Proper_call | | eassumption ].
        repeat intro. exists i. ssplit; eauto. } }
  Qed.
End Proofs.
