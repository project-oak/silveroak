Require Import Arith Eqdep List Lia.

Import ListNotations.
Import EqNotations.

Require Import Cava.BitArithmetic.

Require Import Cava.Types.
Require Import Cava.Arrow.Kappa.Kappa.
Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Instances.Constructive.
Require Import Cava.Arrow.Kappa.Kappa.

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

(* An environment to track the arrow Kinds corresponding to variables.
Variables in a Kappa term are then instantiated as a morphism from the environment
to the Kind found at an index. *)

Definition environment := list Kind. 

Fixpoint as_kind (env: environment): Kind :=
  match env with
  | [] => Unit
  | x :: xs => Tuple x (as_kind xs)
  end.

Fixpoint lookup_kind (env: environment) (i: nat) : option Kind :=
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
  fun  (env: list Kind) (i: nat) (ty: Kind) => env ? i = Some ty
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
    -> ty' <> ty
    -> False.
  Proof. env_auto. Qed.
End env.

(* Construct an Arrow morphism that takes a variable environment
and returns the variable at an index *)
Fixpoint extract_nth (env: environment) ty x
  : (lookup_kind env x = Some ty) -> structure (as_kind env) ty :=
  match env return (lookup_kind env x = Some ty) -> structure (as_kind env) ty with
  | [] => fun H => match lookup_lower_contra H with end
  | ty' :: env' => fun H =>
    match eq_nat_dec x (length env') with
    | left Heq =>
      match decKind ty ty' with
      | left Heq2 => rew <- Heq2 in (Second Drop >>> Cancelr) 
      | right Hneq => match lookup_top_contra _ Heq H Hneq with end
      end
    | right Hneq => First Drop >>> Cancell >>> extract_nth env' x (push_lookup _ _ Hneq H)
    end
  end.

Definition natvar : Kind -> Kind -> Type := fun _ _ => nat.

(* Reverse de Brujin indexing is well formed *)
Fixpoint wf_debrujin {i o}
  (env: environment)
  (expr: @kappa natvar i o) {struct expr}
  : Prop :=
  match expr with
  | DVar i         => ok_lookup env i o
  | @DAbs _ x y z f  => wf_debrujin (x :: env) (f (length env))
  | DApp e1 e2     => wf_debrujin env e1 /\ wf_debrujin env e2
  | DCompose e1 e2 => wf_debrujin env e1 /\ wf_debrujin env e2
  | DArr _         => True
  end.

(****************************************************************************)
(* de Brujin indexing lemmas                                                *)
(****************************************************************************)

Section env.
  Context {env: environment}.

  Lemma wf_debrujin_succ: forall {x y z} f,
    @wf_debrujin (Tuple x y) z env (DAbs f) -> @wf_debrujin y z (x :: env) (f (length env)).
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_compose1: forall {x y z} e1 e2,
    @wf_debrujin x z env (DCompose e2 e1) -> @wf_debrujin x y env e1.
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_compose2: forall {x y z} e1 e2,
    @wf_debrujin x z env (DCompose e2 e1) -> @wf_debrujin y z env e2.
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_app1: forall {x y z} f e,
    wf_debrujin env (DApp f e) -> @wf_debrujin <<x, y>> z env f.
  Proof. env_auto. Qed.

  Lemma wf_debrujin_lax_app2: forall {x y z} f e,
    @wf_debrujin y z env (DApp f e) -> @wf_debrujin Unit x env e.
  Proof. env_auto. Qed.
End env.

(* Perform closure conversion by passing an explicit environment. The higher
order PHOAS representation is converted to first order form with de Brujin
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
  : wf_debrujin env expr -> structure (Tuple i (as_kind env)) o.
    refine (
match expr as expr in kappa _ i' o' return i = i' -> o = o' -> 
wf_debrujin env expr -> structure (Tuple i (as_kind env)) o 
with
| DVar v => fun _ _ wf => First Drop >>> Cancell >>> _
(* Instantiating a variable is done by 'cancell' to select the environment, and
then indexing using lookup_morphism. *)
| @DAbs _ x y z f => fun _ _ wf =>
(* Kappa abstraction requires extending the environment then moving the 
new environment variable in to place*)
  let f' := closure_conversion' _ _ (x :: env) (f (length env)) (wf_debrujin_succ _ wf) in
  (* This line moves the first arrow argument into the right hand position,
  which allows 'assoc' to move the argument to the front of the environment
  f: x*y ~> o

  f_kappa:    (x*y)*environment_variables ~> o
  first swap: (y*x)*environment_variables ~> o
  assoc:      y*(x*environment_variables) ~> o
  f':         y*new_environment_variables ~> o
  *)
  _ (* first swap >>> assoc >>> f' *)

  | DApp f e => fun _ _ wf =>
  (* for application the Kind environment needs to be piped to the abstraction
  'f' and applicant 'e'. since running 'closure_conversion' on each binder
  removes the environment, we first need to copy the environment. *)
  _
  (* second (copy >>> first (uncancell
  >>> closure_conversion' _ _ _ env e (proj2 _)))
  >>> unassoc >>> first swap
  >>> closure_conversion' _ _ _ env f (proj1 _) *)

| DCompose e1 e2 => fun _ _ wf => _
  (* second copy
  >>> unassoc
  >>> first (closure_conversion' env e2 (proj2 wf))
  >>> closure_conversion' env e1 (proj1 wf) *)

| DArr m => fun _ _ _ => _ (* cancelr >>> m *)
end (eq_refl i) (eq_refl o)
).
- unfold wf_debrujin in wf.
  rewrite e0.
  apply (extract_nth env v wf).

- rewrite e, e0.
  exact (first swap >>> assoc >>> f').

- rewrite e0, e1.
  exact (
    second (copy >>> first (uncancell
    >>> closure_conversion' _ _ env e (wf_debrujin_lax_app2 wf)))
    >>> unassoc >>> first swap
    >>> closure_conversion' _ _ env f (wf_debrujin_lax_app1 wf)
  ).
- rewrite e, e0.
  exact (
  second copy
  >>> unassoc
  >>> first (closure_conversion' _ _ env e2 (wf_debrujin_lax_compose1 wf))
  >>> closure_conversion' _ _ env e1 (wf_debrujin_lax_compose2 wf)
).
- rewrite e, e0.
  exact (Second Drop >>> Cancelr >>> m).
Defined.

(****************************************************************************)
(* Kappa term equivalence                                                   *)
(****************************************************************************)

Section Equivalence.
  Inductive obj_tup :  Type := obj_pair : Kind -> Kind -> obj_tup.
  Variables var1 var2 : Kind -> Kind -> Type.

  Definition vars := existT (fun '(obj_pair x y) => (var1 x y * var2 x y)%type).
  Definition ctxt := list { '(obj_pair x y) : obj_tup & (var1 x y * var2 x y)%type }.

  Inductive kappa_equivalence:
    forall i o, ctxt
    -> kappa var1 i o -> kappa var2 i o
    -> Prop :=
  | Var_equiv : forall i o (n1: var1 i o) (n2: var2 i o) E,
    In (vars (obj_pair i o) (pair n1 n2)) E
    -> kappa_equivalence E (DVar n1) (DVar n2)

  | Abs_equiv : forall x y z 
    (f1: var1 Unit x -> kappa var1 y z) 
    (f2: var2 Unit x -> kappa var2 y z) 
    (E:ctxt),
    (forall n1 n2, kappa_equivalence (vars (obj_pair Unit x) (pair n1 n2) :: E) (f1 n1) (f2 n2))
    -> kappa_equivalence E (DAbs f1) (DAbs f2)

  | App_equiv : forall E x y z 
    (f1 : kappa var1 (x**y) z) 
    (f2 : kappa var2 (x**y) z) 
    e1 e2,
    kappa_equivalence E f1 f2
    -> kappa_equivalence E e1 e2
    -> kappa_equivalence E (DApp f1 e1) (DApp f2 e2)

  | Compose_equiv : forall E x y z 
    (f1: kappa var1 y z) (f2: kappa var2 y z)
    (g1: kappa var1 x y) (g2: kappa var2 x y),
    kappa_equivalence E f1 f2
    -> kappa_equivalence E g1 g2
    -> kappa_equivalence E (DCompose f1 g1) (DCompose f2 g2)

  | Arr_equiv : forall x y E (m: morphism x y), kappa_equivalence E (DArr m) (DArr m) .
End Equivalence.

Axiom Kappa_equivalence : forall {i o} (expr: forall var, @kappa var i o) var1 var2,
  kappa_equivalence nil (expr var1) (expr var2).

Notation variable_pair i o n1 n2 := (vars natvar natvar (obj_pair i o) (pair n1 n2)).

(* Evidence of variable pair equality *)
Notation match_pairs xo xn yi yo yn1 yn2 :=
  (variable_pair Unit xo xn xn = variable_pair yi yo yn1 yn2).

(* Evidence that if a given variable is in an environment we can lookup_kind the Kind at the index. *)
Notation ok_variable_lookup := (fun env E =>
  forall (i o : Kind) (n1 n2 : natvar i o),
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