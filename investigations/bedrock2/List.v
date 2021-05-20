Require Import Coq.Lists.List.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.

(* TODO: these lemmas should be merged upstream to coqutil *)

Lemma dedup_length {A} (aeqb : A -> A -> bool) (aeqb_spec : EqDecider aeqb) l :
  length (dedup aeqb l) <= length l.
Proof.
  induction l; [ reflexivity | ].
  cbn [dedup]. destruct_one_match; cbn [length]; Lia.lia.
Qed.

Lemma dedup_NoDup_iff {A} (aeqb : A -> A -> bool) (aeqb_spec : EqDecider aeqb) l :
  dedup aeqb l = l <-> NoDup l.
Proof.
  split.
  { induction l; [ solve [constructor] | ].
    cbn [dedup]. destruct_one_match.
    { intro Heq. pose proof dedup_length aeqb _ l as Hlen.
      rewrite Heq in Hlen. cbn [length] in *; Lia.lia. }
    { inversion 1 as [Heq].
      constructor; [ | rewrite Heq; solve [eauto] ].
      intro Hin. rewrite Heq in Hin.
      lazymatch goal with
      | H : find (aeqb ?x) _ = None |- _ =>
        eapply find_none in H; [ | eapply Hin ];
          destr (aeqb x x)
      end; congruence. } }
  { induction l; [ reflexivity | ].
    inversion 1; subst. cbn [dedup].
    destruct_one_match; [ | rewrite IHl; solve [auto] ].
    lazymatch goal with
    | H : find (aeqb ?x) _ = Some _ |- _ =>
      eapply find_some in H; destruct H
    end.
    lazymatch goal with
      | H : context [aeqb ?x ?y] |- _ =>
        destr (aeqb x y)
    end; congruence. }
Qed.
