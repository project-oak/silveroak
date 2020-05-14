Require Import Arith Eqdep List Lia.

Import ListNotations.

Require Import Cava.BitArithmetic.

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Syntax.Desugared.

Set Implicit Arguments.

Ltac solver :=
  simpl in *; try subst; try match goal with
  | [ H : ?X < ?X |- _ ] => apply Nat.lt_irrefl in H; contradiction
  | [ H : ?X = ?Y, H1: ?X < ?Y |- _ ] => rewrite H in H1; apply Nat.lt_irrefl in H; contradiction

  | [ |- Some ?X = Some ?X ] => f_equal
  | [ |- context[eq_nat_dec ?X ?Y] ] => destruct (eq_nat_dec X Y)

  | [ H : None = Some _|- _ ] => inversion H
  | [ H : Some ?X = Some ?Y |- _ ] => inversion H
  | [ H : ?X /\ ?Y |- _ ] => inversion H; clear H
  | [ H : ?X \/ ?Y |- _ \/ ?Y ] => inversion H; [ left; progress eauto | right; progress eauto ]
  | [ H : ?X \/ ?Y |- _ ] => inversion H; clear H

  | [ H : context[eq_nat_dec ?X ?Y] |- _ ] => destruct (eq_nat_dec X Y)
  | [ H : ?X = ?Y, H2: ?X = ?Y -> ?Z |- _ ] => apply H2 in H

  | [ H : ?X = ?Y, H2: context[?X] |- _ ] => rewrite H in H2

  | [ H : ?X <> ?X |- _ ] => destruct H
  end.

Hint Extern 2 => solver : core.

Hint Extern 4 (_ < length (_ :: _)) => simpl : core.

Section WithArrow.
  Variable arr: Arrow.

  (****************************************************************************)
  (* Environment manipulation                                                 *)
  (****************************************************************************)

  (* An environment to track the arrow objects corresponding to variables.
  Variables are then instantiated as a morphism from the environment to the
  associated object. *)
  Inductive environment : nat -> Type :=
  | ECons : forall n (o: object), environment n -> environment (S n)
  | ENil : environment 0.

  Fixpoint as_object {n} (env: environment n): object :=
  match env with
  | ENil => unit
  | ECons o env' => o ** as_object env'
  end.

  Fixpoint as_object_list {n} (env: environment n): list object :=
  match env with
  | ENil => []
  | ECons o env' => o :: as_object_list env'
  end.

  Fixpoint lookup_object (n: nat) (env: list object): option object :=
  match env with
  | [] => None
  | o :: os =>
    if eq_nat_dec n (length os)
    then Some o
    else lookup_object n os
  end.

  (* The type of an arrow morphism from our environment to a variable is 
  `as_object env ~> o`
  where lookup_object n env = Some o *)
  Fixpoint lookup_morphism_ty (n: nat) (env_obj: object) (objs: list object): Type :=
  match objs with
  | [] => Datatypes.unit
  | o::os =>
    if eq_nat_dec n (length os)
    then morphism env_obj o
    else lookup_morphism_ty n env_obj os
  end.

  (****************************************************************************)
  (* Environment lemmas                                                       *)
  (****************************************************************************)

  Lemma lookup_bound:
    forall n o objs,
    lookup_object n objs = Some o
    -> n < length objs.
  Proof.
    induction objs; auto.
  Qed.

  Hint Extern 3 =>
    match goal with 
    | [H: lookup_object _ _ = Some _|- _] => apply lookup_bound in H as H1
    end : core.

  Lemma lookup_lower_contra : forall o n,
    lookup_object n [] = Some o -> False.
  Proof.
    auto.
  Qed.

  Lemma lookup_upper_contra : forall o objs,
    lookup_object (length objs) objs = Some o -> False.
  Proof.
    auto. 
  Qed.

  Hint Extern 1 => 
    match goal with
    | [H: lookup_object (length ?X) (?X) = Some _ |- _] => apply lookup_upper_contra in H; contradiction
    | [H: lookup_object ?X [] = Some _ |- _] => apply lookup_lower_contra in H; contradiction
    end : core.

  (* Shorthand for passing evidence that a lookup is well formed *)
  Notation ok_lookup := (
    fun (n: nat) (env: list object) (o: object) => lookup_object n env = Some o
  ).

  (* Proof that looking up a morphism is the morphism from the environment to
    * the object at the same index.
    *)
  Lemma ok_lookup_sets_lookup_morphism_ty : forall n o objs env_obj,
    lookup_object n objs = Some o
    -> lookup_morphism_ty n env_obj objs = morphism env_obj o.
  Proof.
    induction objs; auto.
  Defined.

  Hint Immediate ok_lookup_sets_lookup_morphism_ty : core.

  Lemma morphism_coerce:
    forall (n:nat) env_obj o (objs: list object),
    ok_lookup n objs o ->
    lookup_morphism_ty n env_obj objs = morphism env_obj o.
  Proof.
    auto.
  Qed.

  Lemma environment_objects_length_is_n  (n: nat) (env: environment n):
    length (as_object_list env) = n.
  Proof.
    induction env; auto.
  Defined.

  Hint Extern 4 => 
    match goal with
    | [H: context[length(as_object_list ?X)] |- _] => rewrite environment_objects_length_is_n in H
    end : core.

  Lemma split_lookup : forall n env v1 y o,
    ((n = v1 /\ y = o) \/ lookup_object v1 (as_object_list env) = Some o)
    -> lookup_object v1 (as_object_list (@ECons n y env)) = Some o.
  Proof.
    auto 6.
  Qed.

  Lemma unsplit_lookup : forall n env v1 y o,
    lookup_object v1 (as_object_list (@ECons n y env)) = Some o
    ->
    ((n = v1 /\ y = o) \/ lookup_object v1 (as_object_list env) = Some o).
  Proof.
    auto 6.
  Qed.

  Lemma lookup_top_is_extraction: forall n m o o' env x, 
    m = n
    -> lookup_object m (as_object_list (@ECons n o env)) = Some o' 
    -> morphism (o**x) o'.
  Proof.
    Hint Extern 1 => exact exl : core.
    intros.
    rewrite H in H0.
    unfold lookup_object in H0.  
    simpl in H0.
    rewrite environment_objects_length_is_n in H0.
    simpl in H0.
    destruct (Nat.eq_dec n n).
    inversion H0.
    exact exl.
    destruct n0.
    reflexivity.
  Defined.

  Lemma push_lookup : forall n env o o' x ,
    x <> n ->
    lookup_object x (as_object_list (@ECons n o' env)) = Some o ->
    lookup_object x (as_object_list env) = Some o.
  Proof.
    Hint Extern 1 => lia : core.
    auto.
  Qed.

  Fixpoint extract_nth n (env: environment n) o x
    : (lookup_object x (as_object_list env) = Some o) -> morphism (as_object env) o :=
  match env return
    (lookup_object x (as_object_list env) = Some o) -> morphism (as_object env) o
    with
  | ENil => fun H => match lookup_lower_contra H with end
  | @ECons n' o' env' => fun H =>
    match eq_nat_dec x n' with
    | left Heq => (lookup_top_is_extraction  _ env' _ Heq H)
    | right Hneq =>  exr >>> extract_nth env' x (push_lookup _ _ Hneq H)
    end
  end.
  
  (****************************************************************************)
  (* Closure conversion via de Brujin indices form                            *)
  (****************************************************************************)
  (* In de Brujin indexing variables are nats *)

  Definition natvar : object -> object -> Type := fun _ _ => nat.

  (* Reverse de Brujin indexing is well formed *)
  Fixpoint wf_debrujin {i o}
    (n: nat) (env: environment n)
    (expr: kappa natvar i o) {struct expr}
    : Prop :=
  match expr with
  | DVar x            => ok_lookup x (as_object_list env) o
  | @DAbs _ _ x y z f => wf_debrujin (@ECons n x env) (f n)
  | DApp e1 e2        => wf_debrujin env e1 /\ wf_debrujin env e2
  | DCompose e1 e2    => wf_debrujin env e1 /\ wf_debrujin env e2
  | DArr _            => True
  end.

  Lemma wf_debrujin_succ: 
    forall ix iy o 
    (n: nat) (env: environment n)
    (expr: kappa natvar (ix**iy) o)
    f,
    expr = DAbs f ->
    @wf_debrujin (ix**iy) o n env expr -> @wf_debrujin iy o (S n) (ECons ix env) (f n).
  Proof.
    auto.
  Defined.

  (* Perform closure conversion by passing an explicit environment. The higher
  order PHOAS representation is converted to first order form with de Brujin
  indexing as described by Adam Chlipala's Lambda Tamer project. As our source
  language is a Kappa calculus and our target is a Generalized Arrow representation,
  the environment and arguments are manipulated using Arrow combinators amongst
  other differences.

  This implementation is also currently missing logic to remove free variables
  from the environment.
  *)
  Fixpoint closure_conversion {i o}
    (n: nat) (env: environment n)
    (* (morphs: env_morphisms (as_object env) (as_object_list env)) *)
    (expr: kappa natvar i o) {struct expr}
    : wf_debrujin env expr -> morphism (i ** as_object env) o :=
  match expr with
    (* Instantiating a variable is done by 'exr' to select the environment, and
    then indexing using lookup_morphism. 'morphisms_coerce' and 'wf' are used to
    align the types and to prove to Coq that the lookup is well formed. *)
  | DVar v => fun wf => exr >>> extract_nth env v wf
    (* Kappa abstraction requires extending the environment which includes
    modifying all the variable morphisms in scope (and their types!).
    *)
  | @DAbs _ _ x y _ f => fun wf =>
    let env' := ECons x env in
    let f' := closure_conversion env'  (f n) (wf_debrujin_succ _ eq_refl wf) in
    (* This line moves the first arrow argument into the right hand position,
    which allows 'assoc' to move the argument to the front of the environment
    f: x*y ~> o

    f_kappa:    (x*y)*environment_variables ~> o
    first swap: (y*x)*environment_variables ~> o
    assoc:      y*(x*environment_variables) ~> o
    f':         y*new_environment_variables ~> o
    *)
    first swap >>> assoc >>> f'

  (* for application the object environment needs to be piped to the abstraction
  'f' and applicant 'e'. since running 'closure_conversion' on each binder
  removes the environment, we first need to copy the environment.
  *)
  | DApp f e => fun wf =>
    second (copy >>> first (uncancell
    >>> closure_conversion env e (proj2 wf)))
    >>> unassoc >>> first swap
    >>> closure_conversion env f (proj1 wf)

    (* Alternatively *)
    (* copy *)
    (* >>> first (first drop >>> closure_conversion env morphs e (proj2 wf)) *)
    (* >>> unassoc                                     *)
    (* >>> closure_conversion env morphs f (proj1 wf) *)

  (* Similarly for composing two arrows f & g, the object environment needs to be
  * piped to both f and g. So we first need to copy the environment.
  *)
  | DCompose e1 e2 => fun wf =>
    second copy
    >>> unassoc
    >>> first (closure_conversion env e2 (proj2 wf))
    >>> closure_conversion env e1 (proj1 wf)

  | DArr m => fun _ => exl >>> m
  end.

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
    | Var_equiv : forall i o n1 n2 E,
      In (vars (obj_pair i o) (n1,n2)) E
      -> kappa_equivalence E (DVar n1) (DVar n2)

    | Abs_equiv : forall o (f1: var1 unit o -> kappa var1 unit o) f2 (E:ctxt),
      (forall n1 n2, kappa_equivalence (vars (obj_pair unit o) (n1,n2) :: E) (f1 n1) (f2 n2))
      -> kappa_equivalence E (DAbs f1) (DAbs f2)

    | App_equiv : forall E x y z (f1 : kappa var1 (x**y) z) f2 e1 e2,
      kappa_equivalence E f1 f2
      -> kappa_equivalence E e1 e2
      -> kappa_equivalence E (DApp f1 e1) (DApp f2 e2)

    | Compose_equiv : forall E x y z (f1 : kappa var1 y z) f2 (g1: kappa var1 x y) g2,
      kappa_equivalence E f1 f2
      -> kappa_equivalence E g1 g2
      -> kappa_equivalence E (DCompose f1 g1) (DCompose f2 g2)

    | Arr_equiv : forall x y E (m: morphism x y), kappa_equivalence E (DArr m) (DArr m) .
  End Equivalence.

  Axiom Kappa_equivalence : forall {i o} (expr: forall var, kappa var i o) var1 var2,
    kappa_equivalence nil (expr var1) (expr var2).

  Notation variable_pair i o n1 n2 := (vars natvar natvar (obj_pair i o) (n1, n2)).

  (* Evidence of variable pair equality *)
  Notation match_pairs xo xn yi yo yn1 yn2 := 
    (variable_pair unit xo xn xn = variable_pair yi yo yn1 yn2).

  (* Evidence that if a given variable is in an environment we can lookup_object the object at the index. *)
  Notation ok_variable_lookup := (fun env E =>
    forall (i o : object) (n1 n2 : natvar i o),
      In (vars natvar natvar (obj_pair i o) (n1, n2)) E
      -> lookup_object n1 (as_object_list env) = Some o
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

  Lemma apply_lookup : forall n (env: environment n) i o n1 n2 E,
    In (variable_pair i o n1 n2) E
    -> ok_variable_lookup env E
    -> lookup_object n1 (as_object_list env) = Some o.
  Proof.
    Hint Extern 1 => 
      match goal with
      | [H1: In _ ?X, H2: ok_variable_lookup _ ?X |- _] => apply H2 in H1
      end : core.
    auto.
  Qed.
    
  Lemma apply_extended_lookup: forall n env v1 v2 y i o E,
    match_pairs y n i o v1 v2 \/ In (vars natvar natvar (obj_pair i o) (v1, v2)) E
    -> ok_variable_lookup env E
    -> lookup_object v1 (as_object_list (@ECons n y env)) = Some o.
  Proof.
    Hint Extern 3 => eapply recover_dependent_val : core.
    Hint Resolve split_lookup : core.
    eauto 7.
  Qed.

  Hint Immediate apply_lookup : core.
  Hint Immediate apply_extended_lookup : core.

  (* Apply the auto generated kappa_equivalence_ind induction scheme rather than
  calling induction directly as calling induction directly results in too
  specific hypotheses. *)
  Lemma kappa_wf
    : forall i o E (expr1 expr2: kappa natvar i o),
    kappa_equivalence E expr1 expr2
    -> forall n (env: environment n), ok_variable_lookup env E
    -> wf_debrujin env expr1.
  Proof.
    apply (kappa_equivalence_ind
    (fun i o E (expr1 expr2 : kappa natvar i o) =>
      forall n (env: environment n),
        ok_variable_lookup env E
        -> wf_debrujin env expr1)
        ); eauto.
  Qed.

  Hint Resolve kappa_wf : core.
  Hint Resolve Kappa_equivalence : core.

  Theorem Kappa_wf: forall {i o} (expr: forall var, kappa var i o), @wf_debrujin _ _ 0 ENil (expr _).
  Proof.
    eauto.
  Qed.

End WithArrow.

Definition Closure_conversion {arr i o} (expr: @Kappa arr i o): i ~> o
  := uncancelr >>> closure_conversion (ENil arr) (expr _) (Kappa_wf expr).