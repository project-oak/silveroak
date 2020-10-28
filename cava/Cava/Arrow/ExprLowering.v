Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Require Import Cava.Arrow.ExprSyntax.
Require Import Cava.Arrow.ExprEquiv.
Require Import Cava.Arrow.ArrowKind.
Require Import Cava.Arrow.Primitives.
Require Import Cava.Arrow.CircuitArrow.

Require Import Cava.Arrow.Classes.Category.
Require Import Cava.Arrow.Classes.Arrow.

Import ListNotations.
Import EqNotations.

Generalizable All Variables.

(* Section Arrow.

Context {Kind: Type}.
Context {unit: Kind}.
Context {category: Category Kind}.
Context {product: Kind -> Kind -> Kind}.
Context {arrow: Arrow Kind category unit product}.
Context {stkc: ArrowSTKC arrow}.
Context {arrow_loop: ArrowLoop arrow}.
Context {decidable_equality: DecidableEquality Kind}.
Context {default_Kind: forall x, morphism unit x}.
*)
Local Open Scope category_scope.
Local Open Scope arrow_scope.

Set Implicit Arguments.

Create HintDb kappa_cc.

(* immediate contradictions *)
Hint Extern 1 =>
  match goal with
  | [ H : ?X < ?X |- _ ] => apply Nat.lt_irrefl in H; contradiction
  | [ H : ?X = ?Y, H1: ?X < ?Y |- _ ] => rewrite H in H1; apply Nat.lt_irrefl in H; contradiction
  | [ H : ?X <> ?X |- _ ] => destruct H
  | [ H : None = Some _|- _ ] => inversion H
  | [ H : reverse_nth [] _ = Some _|- _ ] => inversion H
  | [ H : In _ [] |- _ ] => inversion H
  end : kappa_cc.

Hint Extern 5 =>
  match goal with
  | [ H : Some ?X = Some ?Y |- _ ] => inversion H; clear H
  | [ H : Some ?X = Some ?Y |- _ ] => inversion H; clear H
  end : kappa_cc.

Hint Extern 10 =>
  match goal with
  | [ H : ?X /\ ?Y |- _ ] => inversion H; clear H
  | [ H : ?X \/ ?Y |- _ ] => inversion H; clear H
  | [ H : ?Y |- _ \/ ?Y ] => right; exact H
  | [ H : ?Y |- ?Y \/ _ ] => left; exact H
  end : kappa_cc.

Hint Extern 15 =>
  match goal with
  | [ H0: length ?Y = ?Z, H1: ?X = ?TY |- reverse_nth (?X :: ?Y) ?Z = Some ?TY ] =>
    unfold reverse_nth;
    let x := fresh in (
      elim (Nat.eq_dec Z (length Y)); intro x;
      [f_equal; exact H1 | rewrite H0 in x; contradiction]
      )
  | [ H: reverse_nth (_ :: ?l) ?i = Some _ |- _ ] => cbn in H; destruct (Nat.eq_dec i (length l))
  | [ H: ?X = length ?Y |- _ ] => rewrite H; clear H
  | [ H0: ?X, H1: ?X -> ?Y |- _ ] => apply H1 in H0
  end : kappa_cc.

Hint Extern 50 => simpl; lia : kappa_cc.

Notation ok_lookup := (fun (l: list _) (n: nat) (ty: _) => reverse_nth l n = Some ty).

Fixpoint as_kind (ctxt: list Kind): Kind :=
  match ctxt with
  | [] => Unit
  | x :: xs => Tuple x (as_kind xs)
  end.

(****************************************************************************)
(* Environmental variable lookup lemmas                                     *)
(****************************************************************************)

Section ctxt.
  Variable ctxt: list Kind.

  Tactic Notation "ctxt_induction" := intros; induction ctxt; auto with kappa_cc.

  Lemma lookup_bound: forall ty i,
    ok_lookup ctxt i ty -> i < length ctxt.
  Proof. ctxt_induction. Qed.

  Hint Extern 55 =>
    match goal with
    | [ H: ?i <length ?ctxt |- reverse_nth (_ :: ?ctxt) ?i = Some ?ty] => cbn; destruct (Nat.eq_dec i (length ctxt))
    | [H: reverse_nth _ _ = Some _|- _] => let x := fresh in apply lookup_bound in H as x
    end : kappa_cc.

  Lemma lookup_lower_contra : forall i ty,
    reverse_nth (A:=Kind) [] i = Some ty -> False.
  Proof. auto with kappa_cc. Qed.

  Lemma lookup_upper_contra : forall ty,
    reverse_nth ctxt (length ctxt) = Some ty -> False.
  Proof. auto with kappa_cc. Qed.

  Hint Extern 1 =>
    match goal with
    | [H: reverse_nth (length ?X) (?X) = Some _ |- _] => apply lookup_upper_contra in H; contradiction
    | [H: reverse_nth ?X [] = Some _ |- _] => apply lookup_lower_contra in H; contradiction
    end : kappa_cc.

  Lemma split_lookup : forall i x ty,
    ((length ctxt = i /\ x = ty) \/ reverse_nth ctxt i = Some ty)
    -> reverse_nth (x :: ctxt) i = Some ty.
  Proof. auto with kappa_cc. Qed.

  Lemma unsplit_lookup : forall i x ty,
    reverse_nth (x :: ctxt) i = Some ty ->
    ((length ctxt = i /\ x = ty) \/ reverse_nth ctxt i = Some ty).
  Proof. auto with kappa_cc. Qed.

  Lemma push_lookup : forall i x ty,
    i <> length ctxt ->
    reverse_nth (x :: ctxt) i = Some ty ->
    reverse_nth ctxt i = Some ty.
  Proof. auto with kappa_cc. Qed.

  Lemma lookup_top_contra: forall i ty ty',
    i = length ctxt
    -> reverse_nth (ty :: ctxt) i = Some ty'
    -> ty <> ty'
    -> False.
  Proof. auto with kappa_cc. Qed.
End ctxt.

(* Construct an Arrow morphism that takes a variable list Kind
and returns the variable at an index *)
Fixpoint extract_nth (ctxt: list Kind) (ty: Kind) (x: nat)
  : (as_kind ctxt) ~[CircuitArrow]~> ty :=
  match ctxt with
  | [] => drop >>> Primitive (Constant _(kind_default _))
  | ty' :: ctxt' =>
    if x =? (length ctxt')
    then second drop >>> cancelr >>> RewriteTy ty' ty
    else first drop >>> cancell >>> extract_nth ctxt' _ x
  end.

(* Perform closure conversion by passing an explicit list Kind. The PHOAS
representation is converted to first order form with de Brujin
indexing as described by Adam Chlipala's Lambda Tamer project. As our source
language is a Kappa calculus and our target is a Generalized Arrow representation,
the list Kind and arguments are manipulated using Arrow combinators amongst
other differences.

This implementation is also currently missing logic to remove free variables
from the list Kind.
*)
Fixpoint closure_conversion' {i o}
  (ctxt: list Kind)
  (expr: kappa natvar i o) {struct expr}
  : (i ** (as_kind ctxt)) ~> o
  :=
match expr with
(* Instantiating a variable is done by 'cancell' to select the list Kind,
and then indexing using lookup_morphism. *)
| Var v =>
  first drop >>> cancell >>> (extract_nth ctxt _ v)

(* Kappa abstraction requires extending the list Kind then moving the
new list Kind variable in to place*)
| Abs f =>
  let f' := closure_conversion' (_ :: ctxt) (f (length ctxt)) in
  (*
      input:      (x*y)*list Kind_variables

  1. 'first swap': Move the first argument into the right hand position
      first swap: (y*x)*list Kind_variables ~> o

  2. 'assoc': move the argument to the front of the list Kind via reassociation
      assoc:      y*(x*list Kind_variables) ~> o

  3. call f'
      f':         y*new_list Kind_variables ~> o
  *)
  first swap >>> assoc >>> f'

(* Application requires the Kind list Kind to be piped to the abstraction
'f' and applicant 'e'. since running 'closure_conversion' on each binder
removes the list Kind, we first need to copy the list Kind. *)
| App f e =>
  second (copy >>> first (uncancell >>> closure_conversion' ctxt e))
  >>> unassoc >>> first swap
  >>> closure_conversion' ctxt f

| Comp e1 e2 =>
  second copy
  >>> unassoc
  >>> first (closure_conversion' ctxt e2)
  >>> closure_conversion' ctxt e1

| ExprSyntax.Primitive p =>
    second drop >>> cancelr >>> (CircuitArrow.Primitive p)

| ExprSyntax.Id =>
    second drop >>> cancelr >>> id

| RemoveContext f =>
  second drop >>> closure_conversion' [] f

| Let v f =>
  let f' := closure_conversion' (_ :: ctxt) (f (length ctxt)) in
  second (copy >>> first (uncancell
  >>> closure_conversion' ctxt v))
  >>> f'

| LetRec v f =>
  let v' := closure_conversion' (_ :: ctxt) (v (length ctxt)) in
  let f' := closure_conversion' (_ :: ctxt) (f (length ctxt)) in

                                  (* i**ctxt ~> o *)
  second (                       (* ctxt ~> o *)
        copy >>>                     (* ctxt*ctxt ~> o *)
        first (                         (* ctxt ~> o *)
          loopl (
          (* z * ctx *)
            first copy >>>
            (* (z * z) ctx  *)
            assoc >>>
            (* z * z * ctx *)
            second (
            (*  z * ctx *)
              uncancell >>>
            (* u * z * ctx *)
              v' >>> uncancelr >>> CircuitArrow.Primitive (Delay _)
            )
            (* z * z' *)
            >>> swap
          )
      )
    )
    >>> f'
end.

Lemma lower_var: forall x (v: _ x) ctxt,
  closure_conversion' ctxt (Var v)
  = first drop >>> cancell >>> (extract_nth ctxt _ v).
Proof. reflexivity. Qed.

Lemma lower_var': forall x (v: _ x) ctxt cv,
  cv = extract_nth ctxt _ v ->
  closure_conversion' ctxt (Var v)
  = first drop >>> cancell >>> cv.
Proof. intros; subst; reflexivity. Qed.

Lemma lower_abs: forall x y z (f: _ x -> kappa _ y z) ctxt,
  closure_conversion' ctxt (Abs f)
  = first swap >>> assoc >>> closure_conversion' (_ :: ctxt) (f (length ctxt)).
Proof. intros; cbn [closure_conversion']; reflexivity. Qed.

Lemma lower_abs': forall x y z (f: _ x -> kappa _ y z) ctxt c1,
  c1 = closure_conversion' (_ :: ctxt) (f (length ctxt)) ->
  closure_conversion' ctxt (Abs f) = first swap >>> assoc >>> c1.
Proof. intros; subst; cbn [closure_conversion']; reflexivity. Qed.

Lemma lower_app: forall x y z (f: kappa _ (Tuple x y) z) e ctxt,
  closure_conversion' ctxt (App f e)
  = second (copy >>> first (uncancell >>> closure_conversion' ctxt e))
  >>> unassoc >>> first swap
  >>> closure_conversion' ctxt f.
Proof. cbn [closure_conversion'];  reflexivity.  Qed.

Lemma lower_app': forall x y z (f: kappa _ (Tuple x y) z) e ctxt c1 c2,
  c1 = closure_conversion' ctxt e ->
  c2 = closure_conversion' ctxt f ->
  closure_conversion' ctxt (App f e)
  = second (copy >>> first (uncancell >>> c1))
  >>> unassoc >>> first swap
  >>> c2.
Proof. intros; subst; cbn [closure_conversion']; reflexivity. Qed.

Lemma lower_comp: forall x y z (e2: kappa _ x y) (e1: kappa _ y z) ctxt,
  closure_conversion' ctxt (Comp e1 e2)
  = second copy
  >>> unassoc
  >>> first (closure_conversion' ctxt e2)
  >>> closure_conversion' ctxt e1.
Proof. intros; subst; cbn [closure_conversion']; reflexivity. Qed.

Lemma lower_comp': forall x y z (e2: kappa _ x y) (e1: kappa _ y z) ctxt c1 c2,
  c1 = closure_conversion' ctxt e1 ->
  c2 = closure_conversion' ctxt e2 ->
  closure_conversion' ctxt (Comp e1 e2)
  = second copy
  >>> unassoc
  >>> first c2
  >>> c1.
Proof. intros; subst; cbn [closure_conversion']; reflexivity. Qed.

Lemma lower_prim: forall p ctxt,
  closure_conversion' ctxt (ExprSyntax.Primitive p)
  = second drop >>> cancelr >>> (CircuitArrow.Primitive p).
Proof. reflexivity. Qed.

Lemma lower_id: forall x ctxt,
  closure_conversion' (i:=x) ctxt ExprSyntax.Id
  = second drop >>> cancelr >>> id.
Proof. reflexivity. Qed.

Lemma lower_remove_context: forall x y (e: kappa _ x y) ctxt,
  closure_conversion' (i:=x) ctxt (RemoveContext e)
  = second drop >>> closure_conversion' [] e.
Proof. reflexivity. Qed.

Lemma lower_remove_context': forall x y (e: kappa _ x y) ctxt c1,
  c1 = closure_conversion' [] e ->
  closure_conversion' (i:=x) ctxt (RemoveContext e)
  = second drop >>> c1.
Proof. intros; subst; cbn [closure_conversion']; reflexivity. Qed.

Lemma lower_let: forall x y z (f: _ x -> kappa _ y z) v ctxt,
  closure_conversion' ctxt (Let v f)
  = second (copy >>> first (uncancell
    >>> closure_conversion' ctxt v))
  >>> (closure_conversion' (_ :: ctxt) (f (length ctxt))).
Proof. reflexivity. Qed.

Lemma lower_let': forall x y z (f: natvar x -> kappa _ y z) v ctxt c1 c2,
  c1 = closure_conversion' ctxt v ->
  c2 = closure_conversion' (_::ctxt) (f (length ctxt)) ->
  closure_conversion' ctxt (Let v f)
  = second (copy >>> first (uncancell >>> c1))
  >>> c2.
Proof. intros; subst; cbn [closure_conversion']; reflexivity. Qed.

Notation variable_pair t n1 n2 := (@vars natvar natvar t (pair n1 n2)).

(* Evidence of variable pair equality *)
Notation match_pairs xt xn yt yn1 yn2 :=
  (variable_pair xt xn xn = variable_pair yt yn1 yn2).

(* Evidence that if a given variable is in an list Kind we can reverse_nth the Kind at the index. *)
Notation ok_variable_lookup := (fun ctxt E =>
  forall (t : Kind) (n1 n2 : natvar t),
    In (vars natvar natvar (pair n1 n2)) E
    -> reverse_nth ctxt n1 = Some t
).

(* Recovering a dependent value requires recovering the type equality first to prevent the
value equality disappearing. *)
Lemma recover_dependent_val: forall xt xn yt yn1 yn2,
  match_pairs xt xn yt yn1 yn2 -> (xn = yn1 /\ xt = yt).
Proof.
  intros.
  inversion H.
  subst.
  generalize (inj_pairT2 _ _ _ _ _ H).
  intro.
  inversion H0.
  auto.
Qed.

Hint Extern 10 =>
  match goal with
  | [H1: In _ ?X, H2: ok_variable_lookup _ ?X |- _] => apply H2 in H1
  end : kappa_cc.

Hint Extern 20 => eapply recover_dependent_val : kappa_cc.

Lemma apply_lookup : forall (ctxt: list Kind) t n1 n2 E,
  In (variable_pair t n1 n2) E
  -> ok_variable_lookup ctxt E
  -> reverse_nth ctxt n1 = Some t.
Proof. auto with kappa_cc. Qed.

Hint Resolve split_lookup : kappa_cc.

Lemma apply_extended_lookup: forall ctxt v1 v2 y t E,
  match_pairs y (length ctxt) t v1 v2 \/ In (@vars natvar natvar t (pair v1 v2)) E
  -> ok_variable_lookup ctxt E
  -> reverse_nth (y :: ctxt) v1 = Some t.
Proof. eauto 7 with kappa_cc. Qed.

Hint Immediate apply_lookup : kappa_cc.
Hint Immediate apply_extended_lookup : kappa_cc.

(* Apply the auto generated kappa_equivalence_ind induction scheme rather than
calling induction directly as calling induction directly results in too
specific hypotheses. *)
Lemma kappa_wf
  : forall i o E (expr1 expr2: kappa natvar i o),
  kappa_equivalence E expr1 expr2
  -> forall (ctxt: list Kind), ok_variable_lookup ctxt E
  -> wf_phoas_context ctxt expr1.
Proof.
  apply (kappa_equivalence_ind
    (fun i o E (expr1 expr2 : kappa natvar i o) =>
      forall (ctxt: list Kind),
        ok_variable_lookup ctxt E
        -> wf_phoas_context ctxt expr1)
    ); simpl; eauto with kappa_cc.
Qed.

Hint Resolve kappa_wf : kappa_cc.

Theorem Kappa_wf: forall {i o} (expr: forall var, kappa var i o),
    Wf expr -> wf_phoas_context [] (expr _).
Proof.
  cbv [Wf]; eauto with kappa_cc.
Qed.

Definition closure_conversion {i o} (expr: Kappa i o) : i ~> o
  := uncancelr >>> closure_conversion' [] (expr _) .

Hint Resolve closure_conversion' : core.
Hint Resolve closure_conversion : core.

(* Provides some idea of term sized caused by context *)
Fixpoint max_context_size' {i o}
  (size: nat)
  (expr: kappa unitvar i o) {struct expr}
  : nat
  :=
match expr with
| Var v => size
| Abs f => max_context_size' (size+1) (f tt)
| App f e => max (max_context_size' size e) (max_context_size' size f)
| Comp e1 e2 => max (max_context_size' size e1) (max_context_size' size e2)
| ExprSyntax.Primitive p => size
| ExprSyntax.Id => size
| RemoveContext f => max size (max_context_size' 0 f)
| Let v f =>
  max (max_context_size' (size+1) (f tt)) (max_context_size' size v)
| LetRec v f =>
  max (max_context_size' (size+1) (f tt)) (max_context_size' (size+1) (v tt))
end.

