Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.letexists.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.Tactics.
Local Open Scope Z_scope.

(* Proofs about cmd.while *)

Section Proofs.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

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
        (post : trace -> mem -> locals -> Prop) :
    repeat_logic_step
      (fun t m l post =>
         exists cond,
           dexpr m l conde cond
           /\ word.unsigned cond <> 0
           /\ cmd (call functions) body t m l post)
      iterations (fun t m l =>
                    exists cond,
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

  (* This lemma handles conditional statements without breaking the entire
     remainder of the function into two goals *)
  Lemma cond_nosplit functions conde ct cf cnext t m l
        (post post_cond : trace -> mem -> locals -> Prop) :
    cmd (call functions) (cmd.cond conde ct cf) t m l post_cond ->
    (forall t m l, post_cond t m l -> cmd (call functions) cnext t m l post) ->
    cmd (call functions) (cmd.seq (cmd.cond conde ct cf) cnext) t m l post.
  Proof.
    cbn [cmd cmd_body]. intros; logical_simplify.
    eexists; ssplit; intros; eauto; [ | ].
    { eapply Proper_cmd; [ apply Proper_call | | solve [eauto] ].
      repeat intro. eauto. }
    { eapply Proper_cmd; [ apply Proper_call | | solve [eauto] ].
      repeat intro. eauto. }
  Qed.
End Proofs.
