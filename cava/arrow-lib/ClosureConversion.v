From Coq Require Import Arith Eqdep List Lia.
From Arrow Require Import Category Arrow Kappa.

Import ListNotations.
Import EqNotations.

Generalizable All Variables.

Section Arrow.

Context `{arrow: Arrow}.
Context {stkc: ArrowSTKC arrow}.
Context {arrow_loop: ArrowLoop arrow}.
Context {object_decidable_equality: forall x y : object, {x = y} + {x <> y}}.

Local Open Scope arrow_scope.

Set Implicit Arguments.

(* todo: make some principled ltac's out of this *)
Ltac solver :=
  simpl in *; try subst; try match goal with
  | [ H : ?X < ?X |- _ ] => apply Nat.lt_irrefl in H; contradiction
  | [ H : ?X = ?Y, H1: ?X < ?Y |- _ ] => rewrite H in H1; apply Nat.lt_irrefl in H; contradiction
  | [ H : ?X <> ?X |- _ ] => destruct H
  | [ H : None = Some _|- _ ] => inversion H

  | [ |- Some ?X = Some ?X ] => f_equal
  | [ |- context[eq_nat_dec ?X ?Y] ] => destruct (eq_nat_dec X Y)

  | [ H : Some ?X = Some ?Y |- _ ] => inversion H
  | [ H : ?X /\ ?Y |- _ ] => inversion H; clear H
  | [ H : ?X \/ ?Y |- _ \/ ?Y ] => inversion H; [ left; progress eauto | right; progress eauto ]
  | [ H : ?X \/ ?Y |- _ ] => inversion H; clear H

  | [ H : context[eq_nat_dec ?X ?Y] |- _ ] => destruct (eq_nat_dec X Y)
  | [ H : ?X = ?Y, H2: ?X = ?Y -> ?Z |- _ ] => apply H2 in H

  | [ H : ?X = ?Y, H2: context[?X] |- _ ] => rewrite H in H2
  end.

Hint Extern 2 => solver : environment.

Ltac env_auto := auto with environment.

(****************************************************************************)
(* Environment manipulation                                                 *)
(****************************************************************************)

(* An environment to track the arrow objects corresponding to variables.
Variables in a Kappa term are then instantiated as a morphism from the environment
to the object found at an index. *)

Definition environment := list object. 

Fixpoint as_kind (env: environment): object :=
  match env with
  | [] => u
  | x :: xs => x ** (as_kind xs)
  end.

Fixpoint lookup_kind (env: environment) (i: nat) : option object :=
  match env with
  | [] => None
  | x :: xs =>
    if eq_nat_dec i (length xs)
    then Some x
    else lookup_kind xs i
  end.

Notation "env ? i" := (lookup_kind env i)(no associativity, at level 50).

(* Shorthand for passing evidence that a lookup is well formed *)
Notation ok_lookup := (
  fun  (env: list object) (i: nat) (ty: object) => env ? i = Some ty
).

(****************************************************************************)
(* Environmental variable lookup lemmas                                     *)
(****************************************************************************)

Section env.
  Variable env: environment.

  Lemma lookup_bound: forall ty i, 
    env ? i = Some ty -> i < length env.
  Proof.
    intros; induction env; env_auto.
  Qed.

  Hint Extern 3 =>
    match goal with
    | [H: lookup_kind _ _ = Some _|- _] => apply lookup_bound in H as H1
    end : environment.

  Lemma lookup_lower_contra : forall i ty,
    lookup_kind [] i = Some ty -> False.
  Proof. env_auto. Qed.

  Lemma lookup_upper_contra : forall ty,
    lookup_kind env (length env) = Some ty -> False.
  Proof. env_auto. Qed.

  Hint Extern 1 =>
    match goal with
    | [H: lookup_kind (length ?X) (?X) = Some _ |- _] => apply lookup_upper_contra in H; contradiction
    | [H: lookup_kind ?X [] = Some _ |- _] => apply lookup_lower_contra in H; contradiction
    end : environment.

  Lemma split_lookup : forall i x ty,
    ((length env = i /\ x = ty) \/ lookup_kind env i = Some ty)
    -> lookup_kind (x :: env) i = Some ty.
  Proof. env_auto. Qed.

  Lemma unsplit_lookup : forall i x ty,
    lookup_kind (x :: env) i = Some ty ->
    ((length env = i /\ x = ty) \/ lookup_kind env i = Some ty).
  Proof. env_auto. Qed.

  Lemma push_lookup : forall i x ty,
    i <> length env ->
    lookup_kind (x :: env) i = Some ty ->
    lookup_kind env i = Some ty.
  Proof. env_auto. Qed.

  Lemma lookup_top_contra: forall i ty ty',
    i = length env
    -> lookup_kind (ty :: env) i = Some ty'
    -> ty <> ty'
    -> False.
  Proof. env_auto. Qed.
End env.

Local Open Scope category_scope.

(* Construct an Arrow morphism that takes a variable environment
and returns the variable at an index *)
Fixpoint extract_nth (env: environment) ty x
  : (lookup_kind env x = Some ty) -> (as_kind env) ~> ty :=
  match env return (lookup_kind env x = Some ty) -> (as_kind env) ~> ty with
  | [] => fun H => match lookup_lower_contra H with end
  | ty' :: env' => fun H =>
    match eq_nat_dec x (length env') with
    | left Heq =>
      match object_decidable_equality ty' ty with
      | left Heq2 => rew Heq2 in (second drop >>> cancelr) 
      | right Hneq => match lookup_top_contra env' Heq H Hneq with end
      end
    | right Hneq => first drop >>> cancell >>> extract_nth env' x (push_lookup _ _ Hneq H)
    end
  end.

Definition natvar : object -> object -> Type := fun _ _ => nat.

(* Reverse de Brujin indexing is well formed *)
Fixpoint wf_debrujin {i o}
  (env: environment)
  (expr: kappa natvar i o) {struct expr}
  : Prop :=
  match expr with
  | Var _ i        => ok_lookup env i o
  | Abs _ x f      => wf_debrujin (x :: env) (f (length env))
  | App _ e1 e2    => wf_debrujin env e1 /\ wf_debrujin env e2
  | Comp _ e1 e2   => wf_debrujin env e1 /\ wf_debrujin env e2
  | Morph _ _      => True
  | LetRec _ x v f => 
    wf_debrujin (x :: env) (v (length env)) /\
    wf_debrujin (x :: env) (f (length env))
  end.

(****************************************************************************)
(* de Brujin indexing lemmas                                                *)
(****************************************************************************)

Section env.
  Context {env: environment}.

  Local Open Scope arrow_scope.

  Lemma wf_debrujin_succ: forall {x y z} f,
    @wf_debrujin (x ** y) z env (Abs _ _ f) -> @wf_debrujin y z (x :: env) (f (length env)).
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_compose1: forall {x y z} e1 e2,
    @wf_debrujin x z env (Comp _ e2 e1) -> @wf_debrujin x y env e1.
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_compose2: forall {x y z} e1 e2,
    @wf_debrujin x z env (Comp _ e2 e1) -> @wf_debrujin y z env e2.
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_app1: forall {x y z} f e,
    wf_debrujin env (App _ f e) -> @wf_debrujin (x ** y) z env f.
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_app2: forall {x y z} f e,
    @wf_debrujin y z env (App _ f e) -> @wf_debrujin u x env e.
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_letrec1: forall {x y z} v f,
    @wf_debrujin y z env (LetRec natvar x v f)
    -> @wf_debrujin u x (x :: env) (v (length env)).
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_letrec2: forall {x y z} v f,
    @wf_debrujin y z env (LetRec natvar x v f)
    -> @wf_debrujin y z (x :: env) (f (length env)).
  Proof. env_auto. Qed.
End env.

(* Perform closure conversion by passing an explicit environment. The PHOAS 
representation is converted to first order form with de Brujin
indexing as described by Adam Chlipala's Lambda Tamer project. As our source
language is a Kappa calculus and our target is a Generalized Arrow representation,
the environment and arguments are manipulated using Arrow combinators amongst
other differences.

This implementation is also currently missing logic to remove free variables
from the environment.
*)
Fixpoint closure_conversion' {i o}
  (env: environment)
  (expr: kappa natvar i o) {struct expr}
  : wf_debrujin env expr -> (i ** (as_kind env)) ~> o
  :=
match expr as expr in kappa _ i' o' return 
  i' ** (as_kind env) = i ** (as_kind env)
  -> o' = o
  -> wf_debrujin env expr -> (i ** (as_kind env)) ~> o 
with
(* Instantiating a variable is done by 'cancell' to select the environment, 
and then indexing using lookup_morphism. *)
| Var _ v => fun _ H wf => rew H in 
  (first drop >>> cancell >>> (extract_nth env v wf))

(* Kappa abstraction requires extending the environment then moving the 
new environment variable in to place*)
| Abs _ x f => fun H1 H2 wf =>
  let f' := closure_conversion' (x :: env) (f (length env)) (wf_debrujin_succ _ wf) in
  (* 
      input:      (x*y)*environment_variables 

  1. 'first swap': Move the first argument into the right hand position
      first swap: (y*x)*environment_variables ~> o
      
  2. 'assoc': move the argument to the front of the environment via reassociation
      assoc:      y*(x*environment_variables) ~> o

  3. call f'
      f':         y*new_environment_variables ~> o
  *)
  let ex := (rew H2 in (first swap >>> assoc >>> f')) in
  rew [fun ty => ty ~> o] H1 in ex

(* Application requires the object environment to be piped to the abstraction
'f' and applicant 'e'. since running 'closure_conversion' on each binder
removes the environment, we first need to copy the environment. *)
| App _ f e => fun H1 H2 wf => 
  rew [fun ty => ty ~> o] H1 in (
    rew H2 in (
      second (copy >>> first (uncancell
      >>> closure_conversion' env e (wf_debrujin_lax_app2 wf)))
      >>> unassoc >>> first swap
      >>> closure_conversion' env f (wf_debrujin_lax_app1 wf)
    ))

| Comp _ e1 e2 => fun H1 H2 wf => 
  rew [fun ty => ty ~> o] H1 in (
    rew H2 in (
      second copy
      >>> unassoc
      >>> first (closure_conversion' env e2 (wf_debrujin_lax_compose1 wf))
      >>> closure_conversion' env e1 (wf_debrujin_lax_compose2 wf)
    ))

| Morph _ m => fun H1 H2 wf => 
  rew [fun ty => ty ~> o] H1 in (
    rew H2 in (
      second drop >>> cancelr >>> m
    ))

| LetRec _ x v f => fun H1 H2 wf =>

  let v' := closure_conversion' (x :: env) (v (length env)) (wf_debrujin_lax_letrec1 wf) in
  let f' := closure_conversion' (x :: env) (f (length env)) (wf_debrujin_lax_letrec2 wf) in

  rew [fun ty => ty ~> o] H1 in (
    rew H2 in (
    (* i**env ~> o *)
    second (
      (* env ~> o *)
      copy >>>
      (* env*env ~> o *)
      first (
        (* env ~> o *)
        uncancell >>> 
          (* u*env ~> o *)
          loopr (assoc >>> second swap >>> v' >>> copy)
      )
      (* i'**env ~> o *)
    )
    (* i**(i'**env) ~> o *)
    >>> f'
  ))
end eq_refl eq_refl.

(****************************************************************************)
(* Kappa term equivalence                                                   *)
(****************************************************************************)

Section Equivalence.
  Inductive obj_tup :  Type := obj_pair : object -> object -> obj_tup.
  Variables var1 var2 : object -> object -> Type.

  Definition vars := existT (fun '(obj_pair x y) => (var1 x y * var2 x y)%type).
  Definition ctxt := list { '(obj_pair x y) : obj_tup & (var1 x y * var2 x y)%type }.

  Inductive kappa_equivalence:
    forall i o, ctxt
    -> kappa var1 i o -> kappa var2 i o
    -> Prop :=
  | Var_equiv : forall i o (n1: var1 i o) (n2: var2 i o) E,
    In (vars (obj_pair i o) (pair n1 n2)) E
    -> kappa_equivalence E (Var _ n1) (Var _ n2)

  | Abs_equiv : forall x y z 
    (f1: var1 u x -> kappa var1 y z) 
    (f2: var2 u x -> kappa var2 y z) 
    (E:ctxt),
    (forall n1 n2, kappa_equivalence (vars (obj_pair u x) (pair n1 n2) :: E) (f1 n1) (f2 n2))
    -> kappa_equivalence E (Abs _ _ f1) (Abs _ _ f2)

  | App_equiv : forall E x y z 
    (f1 : kappa var1 (x**y) z) 
    (f2 : kappa var2 (x**y) z) 
    e1 e2,
    kappa_equivalence E f1 f2
    -> kappa_equivalence E e1 e2
    -> kappa_equivalence E (App _ f1 e1) (App _ f2 e2)

  | Compose_equiv : forall E x y z 
    (f1: kappa var1 y z) (f2: kappa var2 y z)
    (g1: kappa var1 x y) (g2: kappa var2 x y),
    kappa_equivalence E f1 f2
    -> kappa_equivalence E g1 g2
    -> kappa_equivalence E (Comp _ f1 g1) (Comp _ f2 g2)

  | Morph_equiv : forall x y E (m: morphism x y), kappa_equivalence E (Morph _ m) (Morph _ m)

  | Letrec_equiv : forall x y z 
    (v1: var1 u x -> kappa var1 u x) 
    (v2: var2 u x -> kappa var2 u x) 
    (f1: var1 u x -> kappa var1 y z) 
    (f2: var2 u x -> kappa var2 y z) 
    (E:ctxt),
    (forall n1 n2, kappa_equivalence (vars (obj_pair u x) (pair n1 n2) :: E) (v1 n1) (v2 n2))
    -> 
    (forall n1 n2, kappa_equivalence (vars (obj_pair u x) (pair n1 n2) :: E) (f1 n1) (f2 n2))
    -> 
    kappa_equivalence E (LetRec _ _ v1 f1) (LetRec _ _ v2 f2).
End Equivalence.

Axiom Kappa_equivalence : forall {i o} (expr: forall var, kappa var i o) var1 var2,
  kappa_equivalence nil (expr var1) (expr var2).

Notation variable_pair i o n1 n2 := (vars natvar natvar (obj_pair i o) (pair n1 n2)).

(* Evidence of variable pair equality *)
Notation match_pairs xo xn yi yo yn1 yn2 :=
  (variable_pair u xo xn xn = variable_pair yi yo yn1 yn2).

(* Evidence that if a given variable is in an environment we can lookup_kind the object at the index. *)
Notation ok_variable_lookup := (fun env E =>
  forall (i o : object) (n1 n2 : natvar i o),
    In (vars natvar natvar (obj_pair i o) (pair n1 n2)) E
    -> lookup_kind env n1 = Some o
).

Hint Extern 1 =>
  match goal with
  | [H1: In _ ?X, H2: ok_variable_lookup _ ?X |- _] => apply H2 in H1
  end : environment.

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

Hint Extern 3 => eapply recover_dependent_val : environment.

Lemma apply_lookup : forall (env: environment) i o n1 n2 E,
  In (variable_pair i o n1 n2) E
  -> ok_variable_lookup env E
  -> lookup_kind env n1 = Some o.
Proof.
  env_auto.
Qed.

Hint Resolve split_lookup : environment.

Lemma apply_extended_lookup: forall env v1 v2 y i o E,
  match_pairs y (length env) i o v1 v2 \/ In (vars natvar natvar (obj_pair i o) (pair v1 v2)) E
  -> ok_variable_lookup env E
  -> lookup_kind (y :: env) v1 = Some o.
Proof.
  eauto 7 with environment.
Qed.

Hint Immediate apply_lookup : core.
Hint Immediate apply_extended_lookup : core.

(* Apply the auto generated kappa_equivalence_ind induction scheme rather than
calling induction directly as calling induction directly results in too
specific hypotheses. *)
Lemma kappa_wf
  : forall i o E (expr1 expr2: kappa natvar i o),
  kappa_equivalence E expr1 expr2
  -> forall (env: environment), ok_variable_lookup env E
  -> wf_debrujin env expr1.
Proof.
  apply (kappa_equivalence_ind
  (fun i o E (expr1 expr2 : kappa natvar i o) =>
    forall (env: environment),
      ok_variable_lookup env E
      -> wf_debrujin env expr1)
      ); eauto with environment.
Qed.

Hint Resolve kappa_wf : core.
Hint Resolve Kappa_equivalence : core.

Theorem Kappa_wf: forall {i o} (expr: forall var, kappa var i o), @wf_debrujin _ _ [] (expr _).
Proof.
  intros.
  eapply kappa_wf.
  apply Kappa_equivalence.
  intros.
  inversion H.
Qed.

Definition closure_conversion {i o} (expr: Kappa i o) (wf: wf_debrujin [] (expr _)): i ~> o
  := uncancelr >>> closure_conversion' [] (expr _) wf.

Definition Closure_conversion {i o} (expr: Kappa i o): i ~> o
  := closure_conversion expr (Kappa_wf expr).

Hint Resolve closure_conversion' : core.
Hint Resolve closure_conversion : core.
Hint Resolve Closure_conversion : core.

End Arrow.

Ltac wf_kappa_via_compute :=
  compute;
  tauto.

Ltac wf_kappa_via_equiv :=
  match goal with
  | [ |- wf_debrujin _ _] => eapply (@kappa_wf _ _ nil%list)
  end; intros;
  repeat match goal with 
  | [ |- kappa_equivalence _ _ _] => constructor;intros
  end; 
  repeat match goal with 
  | [ H: In _ nil |- _] => inversion H
  | [ |- In _ _ ] => simpl; tauto
  end.
