From Coq Require Import List Peano_dec.
From Arrow Require Import Category Arrow.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.


Section Arrow.
  Context `{arrow: Arrow}.

  Notation object_pair := (object * object)%type.
  Definition natvar : object -> object -> Type := fun _ _ => nat.
  Definition unitvar : object -> object -> Type := fun _ _ => unit.

  Section Vars.
    Variable (var: object -> object -> Type).

    Inductive kappa : object -> object -> Type :=
    | Var : forall {x y},   var x y -> kappa x y
    | Abs : forall {x y z}, (var u x -> kappa y z) -> kappa (product x y) z
    | App : forall {x y z}, kappa (product x y) z -> kappa u x -> kappa y z
    | Comp: forall {x y z}, kappa y z -> kappa x y -> kappa x z
    | Morph : forall {x y}, morphism x y -> kappa x y
    | Let: forall {x y z}, kappa u x -> (var u x -> kappa y z) -> kappa y z
    | LetRec : forall {x y z}, (var u x -> kappa u x) -> (var u x -> kappa y z) -> kappa y z.
  End Vars.

  Fixpoint reverse_nth {A} (l: list A) (n: nat) {struct l}: option A := 
    match l with
    | [] => None
    | x :: xs => 
      match eq_nat_dec n (length xs) with
      | left _ => Some x
      | right Hneq => reverse_nth xs n
      end
    end.

  Notation ok_lookup := (fun (l: list _) (n: nat) (ty: _) => reverse_nth l n = Some ty).

  Fixpoint wf_phoas_context {i o}
    (ctxt: list object)
    (expr: kappa natvar i o) {struct expr}
    : Prop :=
    match expr with
    | Var _ _ n  => ok_lookup ctxt n o
    | Abs x _ _ f => wf_phoas_context (x :: ctxt) (f (length ctxt))
    | App _ _ _ e1 e2 => wf_phoas_context ctxt e1 /\ wf_phoas_context ctxt e2 
    | Comp _ _ _ e1 e2 => wf_phoas_context ctxt e1 /\ wf_phoas_context ctxt e2
    | Morph _ _ _ => True
    | Let x _ _ v f => wf_phoas_context (x :: ctxt) (f (length ctxt)) /\ wf_phoas_context ctxt v 
    | LetRec x _ _ v f => wf_phoas_context (x :: ctxt) (v (length ctxt)) /\ wf_phoas_context (x :: ctxt) (f (length ctxt))
    end.

  Section ctxt.
    Context {ctxt: list object}.
  
    Lemma wf_phoas_context_lax_abs: forall {x y z} f,
      @wf_phoas_context (product x y) z ctxt (Abs f) -> @wf_phoas_context y z (x :: ctxt) (f (length ctxt)).
    Proof. auto. Qed.

    Hint Extern 10 => 
      match goal with
      | [H: wf_phoas_context (_ :: ?ctxt) (Var _ ?v) |- _] => 
        unfold wf_phoas_context, reverse_nth in H;
        destruct (PeanoNat.Nat.eq_dec v (length ctxt))
      | [H: wf_phoas_context _ _ |- _] => inversion H
      end : core.
  
    Lemma wf_phoas_context_lax_var: forall {x y a} v ,
      wf_phoas_context (i:=x) (o:=y) (a :: ctxt) (Var _ v) -> wf_phoas_context ctxt (Var _ v) \/ v = length ctxt.
    Proof. auto. Qed.
  
    Lemma wf_phoas_context_lax_compose1: forall {x y z} e1 e2,
      @wf_phoas_context x z ctxt (Comp e2 e1) -> @wf_phoas_context x y ctxt e1.
    Proof. auto. Qed.
  
    Lemma wf_phoas_context_lax_compose2: forall {x y z} e1 e2,
      @wf_phoas_context x z ctxt (Comp e2 e1) -> @wf_phoas_context y z ctxt e2.
    Proof. auto. Qed.
  
    Lemma wf_phoas_context_lax_app1: forall {x y z} f e,
      wf_phoas_context ctxt (App f e) -> @wf_phoas_context (product x y) z ctxt f.
    Proof. auto. Qed.
  
    Lemma wf_phoas_context_lax_app2: forall {x y z} f e,
      @wf_phoas_context y z ctxt (App f e) -> @wf_phoas_context u x ctxt e.
    Proof. auto. Qed.

    Lemma wf_phoas_context_lax_let1: forall {x y z} v f,
      @wf_phoas_context y z ctxt (Let v f)
      -> @wf_phoas_context u x ctxt v.
    Proof. auto. Qed.

    Lemma wf_phoas_context_lax_let2: forall {x y z} v f,
      @wf_phoas_context y z ctxt (Let (x:=x) v f)
      -> @wf_phoas_context y z (x :: ctxt) (f (length ctxt)).
    Proof. auto. Qed.
  
    Lemma wf_phoas_context_lax_letrec1: forall {x y z} v f,
      @wf_phoas_context y z ctxt (LetRec v f)
      -> @wf_phoas_context u x (x :: ctxt) (v (length ctxt)).
    Proof. auto. Qed.
  
    Lemma wf_phoas_context_lax_letrec2: forall {x y z} v f,
      @wf_phoas_context y z ctxt (LetRec (x:=x) v f)
      -> @wf_phoas_context y z (x :: ctxt) (f (length ctxt)).
    Proof. auto. Qed.
  End ctxt.
    

  Fixpoint wf_phoas_context_elim {i o}
    (ctxt: list object)
    (expr: kappa natvar i o) {struct expr}
    : Prop :=
    match expr with
    | Var _ _ n  => ok_lookup ctxt n o
    | Abs x _ _ f => wf_phoas_context_elim (x :: ctxt) (f (length ctxt))
    | App _ _ _ e1 e2 => forall (p: Prop),
      (wf_phoas_context_elim ctxt e1 -> wf_phoas_context_elim ctxt e2 -> p) -> p
    | Comp _ _ _ e1 e2 => forall (p: Prop),
      (wf_phoas_context_elim ctxt e1 -> wf_phoas_context_elim ctxt e2 -> p) -> p
    | Morph _ _ _ => True
    | Let x _ _ v f => forall (p: Prop), 
      (wf_phoas_context_elim ctxt v -> wf_phoas_context_elim (x :: ctxt) (f (length ctxt)) -> p) -> p
    | LetRec x _ _ v f => forall (p: Prop),
      (wf_phoas_context_elim (x :: ctxt) (v (length ctxt))
      -> wf_phoas_context_elim (x :: ctxt) (f (length ctxt)) -> p) -> p
    end.

  Goal forall x, wf_phoas_context [] (Abs (x:=x) (y:=u) (z:=x) (fun x => Let (Var _ x) (fun y => Var _ y))).
  Proof. cbn; auto. Qed.
  Goal forall x, wf_phoas_context_elim [] (Abs (x:=x) (y:=u) (z:=x) (fun x => Let (Var _ x) (fun y => Var _ y))).
  Proof. cbn; auto. Qed.

  Lemma phoas_context_elim {i o} (expr: kappa natvar i o): forall (ctxt: list object),
    wf_phoas_context_elim ctxt expr -> wf_phoas_context ctxt expr.
  Proof.
    induction expr; cbn [wf_phoas_context_elim] in *; 
      simpl; intros;
      try constructor;
      try apply H;
      try apply H0;
      try apply H1;
      auto.
  Qed.

  Lemma wf_let_is_wf_app_abs {x i o}
    (v: kappa natvar u x)
    (f: natvar u x -> kappa natvar i o)
    : forall (ctxt: list object), wf_phoas_context ctxt (Let v f) -> wf_phoas_context ctxt (App (Abs f) v).
  Proof. now cbn. Qed.
  
  Fixpoint no_letrec {i o} (e: kappa unitvar i o): bool :=
    match e with 
    | Var _ _ _ => true 
    | Abs _ _ _ f => no_letrec (f tt)
    | App _ _ _ f e => no_letrec f && no_letrec e 
    | Comp _ _ _ e1 e2 => no_letrec e1 && no_letrec e2
    | Morph _ _ _ => true
    | Let _ _ _ v f => no_letrec v && no_letrec (f tt) 
    | LetRec _ _ _ f1 f2 => false
    end.

  Fixpoint morph_prop {i o}
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

  Definition Kappa i o := forall var, kappa var i o.

  (* common functions *)

  Open Scope category_scope.
  Context {arrow_drop: ArrowDrop arrow}.

  Definition kappa_fst {var x y}: kappa var (product (product x y) u) x := 
    Morph var (cancelr >>> second drop >>> cancelr).
  Definition kappa_snd {var x y}: kappa var (product (product x y) u) y := 
    Morph var (cancelr >>> first drop >>> cancell).
  Definition kappa_pair {var x y}: kappa var (product x (product y u)) (product x y) := 
    Morph var (second cancelr).

End Arrow.

Ltac dispatch_wf_phoas_context := 
  apply phoas_context_elim;
  lazy -[reverse_nth];
  repeat lazymatch goal with
  | [ |- True ] => constructor
  | [ |- forall p, (?H1 -> ?H2 -> p) -> p ] => 
    let x := fresh in (let y := fresh in (
      intros x y; apply y; clear x y
    ))
  end; 
  repeat lazymatch goal with
  | [ |- reverse_nth _ _ = Some _] => exact eq_refl
  end. 

Arguments Kappa.Var {_ _ _ _ _ var _ _}.
Arguments Kappa.Abs {_ _ _ _ _ var _ _ _}.
Arguments Kappa.App {_ _ _ _ _ var _ _ _}.
Arguments Kappa.Comp {_ _ _ _ _ var _ _ _}.
Arguments Kappa.Morph {_ _ _ _ _ var _ _}.
Arguments Kappa.LetRec {_ _ _ _ _ var _ _ _}.