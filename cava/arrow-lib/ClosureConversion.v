From Coq Require Import Arith Eqdep List Lia.
From Arrow Require Import Category Arrow Kappa KappaEquiv.

Import ListNotations.
Import EqNotations.

Generalizable All Variables.

Section Arrow.

Context {object: Type}.
Context {u: object}.
Context {category: Category object}.
Context {product: object -> object -> object}.
Context {arrow: Arrow object category u product}.
Context {stkc: ArrowSTKC arrow}.
Context {arrow_loop: ArrowLoop arrow}.

Context {decidable_equality: DecidableEquality object}.

Context {default_object: forall x, morphism u x}.

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

Fixpoint as_kind (ctxt: list object): object :=
  match ctxt with
  | [] => u
  | x :: xs => x ** (as_kind xs)
  end.

(****************************************************************************)
(* Environmental variable lookup lemmas                                     *)
(****************************************************************************)

Section ctxt.
  Variable ctxt: list object.

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
    reverse_nth (A:=object) [] i = Some ty -> False.
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

Definition rewrite_object {x y: object} (H: x = y) 
  : x ~> y :=
  match eq_dec x y with
  | left Heq => rew Heq in id
  | right Hneq => (ltac:(abstract contradiction))
  end.

(* Construct an Arrow morphism that takes a variable list object
and returns the variable at an index *)
Fixpoint extract_nth (ctxt: list object) (ty: object) (x: nat)
  : (as_kind ctxt) ~> ty :=
  match ctxt with
  | [] => drop >>> default_object _
  | ty' :: ctxt' =>
    if x =? (length ctxt') then
      match eq_dec ty' ty with
      | left Heq2 => rew Heq2 in (second drop >>> cancelr) 
      | right Hneq => drop >>> default_object _
      end
    else first drop >>> cancell >>> extract_nth ctxt' _ x
  end.

(* Perform closure conversion by passing an explicit list object. The PHOAS 
representation is converted to first order form with de Brujin
indexing as described by Adam Chlipala's Lambda Tamer project. As our source
language is a Kappa calculus and our target is a Generalized Arrow representation,
the list object and arguments are manipulated using Arrow combinators amongst
other differences.

This implementation is also currently missing logic to remove free variables
from the list object.
*)
Fixpoint closure_conversion' {i o}
  (ctxt: list object)
  (expr: kappa natvar i o) {struct expr}
  : (i ** (as_kind ctxt)) ~> o
  :=
match expr with
(* Instantiating a variable is done by 'cancell' to select the list object, 
and then indexing using lookup_morphism. *)
| Var v => 
  first drop >>> cancell >>> (extract_nth ctxt _ v) 

(* Kappa abstraction requires extending the list object then moving the 
new list object variable in to place*)
| Abs f => 
  let f' := closure_conversion' (_ :: ctxt) (f (length ctxt)) in
  (* 
      input:      (x*y)*list object_variables 

  1. 'first swap': Move the first argument into the right hand position
      first swap: (y*x)*list object_variables ~> o
      
  2. 'assoc': move the argument to the front of the list object via reassociation
      assoc:      y*(x*list object_variables) ~> o

  3. call f'
      f':         y*new_list object_variables ~> o
  *)
  first swap >>> assoc >>> f' 

(* Application requires the object list object to be piped to the abstraction
'f' and applicant 'e'. since running 'closure_conversion' on each binder
removes the list object, we first need to copy the list object. *)
| App f e => 
  second (copy >>> first (uncancell >>> closure_conversion' ctxt e))
  >>> unassoc >>> first swap
  >>> closure_conversion' ctxt f

| Comp e1 e2 => 
  second copy
  >>> unassoc
  >>> first (closure_conversion' ctxt e2)
  >>> closure_conversion' ctxt e1

| Morph m => 
    second drop >>> cancelr >>> m

| Let v f => 
  let f' := closure_conversion' (_ :: ctxt) (f (length ctxt)) in
  second (copy >>> first (uncancell
  >>> closure_conversion' ctxt v))
  >>> unassoc >>> first swap
  >>> first swap >>> assoc >>> f'

| LetRec v f => 
  let v' := closure_conversion' (_ :: ctxt) (v (length ctxt)) in
  let f' := closure_conversion' (_ :: ctxt) (f (length ctxt)) in

                                  (* i**ctxt ~> o *)
  second (                       (* ctxt ~> o *)
        copy >>>                     (* ctxt*ctxt ~> o *)
        first (                         (* ctxt ~> o *)
          uncancell >>>                 (* u*ctxt ~> o *)
          loopr (assoc >>> second swap >>> v' >>> copy)
      )                               
    )                              
    >>> f'
end.

Notation variable_pair i o n1 n2 := (vars natvar natvar (obj_pair i o) (pair n1 n2)).

(* Evidence of variable pair equality *)
Notation match_pairs xo xn yi yo yn1 yn2 :=
  (variable_pair u xo xn xn = variable_pair yi yo yn1 yn2).

(* Evidence that if a given variable is in an list object we can reverse_nth the object at the index. *)
Notation ok_variable_lookup := (fun ctxt E =>
  forall (i o : object) (n1 n2 : natvar i o),
    In (vars natvar natvar (obj_pair i o) (pair n1 n2)) E
    -> reverse_nth ctxt n1 = Some o
).

(* Recovering a dependent value requires recovering the type equality first to prevent the
value equality disappearing. *)
Lemma recover_dependent_val: forall xo xn yi yo yn1 yn2,
  match_pairs xo xn yi yo yn1 yn2 -> (xn = yn1 /\ xo = yo).
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

Lemma apply_lookup : forall (ctxt: list object) i o n1 n2 E,
  In (variable_pair i o n1 n2) E
  -> ok_variable_lookup ctxt E
  -> reverse_nth ctxt n1 = Some o.
Proof. auto with kappa_cc. Qed.

Hint Resolve split_lookup : kappa_cc.

Lemma apply_extended_lookup: forall ctxt v1 v2 y i o E,
  match_pairs y (length ctxt) i o v1 v2 \/ In (vars natvar natvar (obj_pair i o) (pair v1 v2)) E
  -> ok_variable_lookup ctxt E
  -> reverse_nth (y :: ctxt) v1 = Some o.
Proof. eauto 7 with kappa_cc. Qed.

Hint Immediate apply_lookup : kappa_cc.
Hint Immediate apply_extended_lookup : kappa_cc.

(* Apply the auto generated kappa_equivalence_ind induction scheme rather than
calling induction directly as calling induction directly results in too
specific hypotheses. *)
Lemma kappa_wf
  : forall i o E (expr1 expr2: kappa natvar i o),
  kappa_equivalence E expr1 expr2
  -> forall (ctxt: list object), ok_variable_lookup ctxt E
  -> wf_phoas_context ctxt expr1.
Proof.
  apply (kappa_equivalence_ind
    (fun i o E (expr1 expr2 : kappa natvar i o) =>
      forall (ctxt: list object),
        ok_variable_lookup ctxt E
        -> wf_phoas_context ctxt expr1)
    ); simpl; eauto with kappa_cc.
Qed.

Hint Resolve kappa_wf : kappa_cc.

Theorem Kappa_wf: forall {i o} (expr: forall var, kappa var i o), wf_phoas_context [] (expr _).
Proof. 
  Hint Extern 5 (kappa_equivalence _ _ _) => apply Kappa_equivalence : kappa_cc.
  eauto with kappa_cc.
Qed.

Definition closure_conversion {i o} (expr: Kappa i o) : i ~> o
  := uncancelr >>> closure_conversion' [] (expr _) .

Hint Resolve closure_conversion' : core.
Hint Resolve closure_conversion : core.

End Arrow.