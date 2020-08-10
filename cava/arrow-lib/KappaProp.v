From Coq Require Import List Peano_dec.
From Arrow Require Import Category Arrow Kappa.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Arrow.
  Context `{arrow: Arrow}.

  Fixpoint no_letrec i o (e: kappa unitvar i o): bool :=
    match e with 
    | Var _ _ _ => true 
    | Abs _ _ _ f => no_letrec (f tt)
    | App _ _ _ f e => no_letrec f && no_letrec e 
    | Comp _ _ _ e1 e2 => no_letrec e1 && no_letrec e2
    | Morph _ _ _ => true
    | Let _ _ _ v f => no_letrec v && no_letrec (f tt) 
    | LetRec _ _ _ f1 f2 => false
    end.

  Fixpoint morph_prop i o
    (P: forall x y, morphism x y -> Prop)
    (e: kappa unitvar i o)
    : Prop :=
    match e with 
    | Var _ _ _ => True 
    | Abs _ _ _ f => morph_prop P (f tt)
    | App _ _ _ f e => forall p: Prop, (morph_prop P f -> morph_prop P e -> p) -> p
    | Comp _ _ _ e1 e2 => forall p: Prop, (morph_prop P e1 -> morph_prop P e2 -> p) -> p
    | Morph _ _ m => P _ _ m
    | Let _ _ _ v f => forall p: Prop, (morph_prop P v -> morph_prop P (f tt) -> p) -> p
    | LetRec _ _ _ f1 f2 => forall p: Prop, (morph_prop P (f1 tt) -> morph_prop P (f2 tt) -> p) -> p
    end.

    Open Scope category_scope.
    Open Scope arrow_scope.

    (* In previous definitions these implications were not immediate,
    are they worth keeping now they mostly follow from 'simpl' ? *)
    Lemma morph_prop_abs: forall {x y z k} p,
      morph_prop p (i:=x ** y) (Abs k) -> 
      morph_prop p (o:=z) (k tt).
    Proof. auto. Qed.

    Lemma morph_prop_app: forall {x y z f e} p,
      morph_prop p (App f e) -> 
      morph_prop p (i:=(x**y)) (o:=z) f /\
      morph_prop p e.
    Proof. simpl; intros. apply H. auto. Qed.

    Lemma morph_prop_comp: forall {x y z e1 e2} p,
      morph_prop p (i:=x) (o:=z) (Comp e1 e2) -> 
      morph_prop p (i:=y) e1 /\
      morph_prop p e2.
    Proof. simpl; intros. apply H. auto. Qed.

    Lemma morph_prop_morph: forall {x y} (m : x~>y) p,
      morph_prop p (Morph m) -> 
      p _ _ m.
    Proof. auto. Qed.
End Arrow.