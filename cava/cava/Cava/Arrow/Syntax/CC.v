Require Import Arith Eqdep List Lia.

Import ListNotations.

Require Import Cava.BitArithmetic.

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Syntax.Desugared.

Set Implicit Arguments.

Section WithArrow.
  Variable arr: Arrow.

  (*
  An environment to track the arrow objects corresponding to variables.
  Variables are then instantiated as a morphism from the environment to the
  associated object.
  *)
  Inductive environment : nat -> Type :=
  | ECons : forall n (o: object), environment n -> environment (S n)
  | ENil : environment 0.

  (****************************************************************************)
  (* Environment manipulation                                                 *)
  (****************************************************************************)

  Fixpoint environment_as_object {n} (env: environment n): object :=
  match env with
  | ENil => unit
  | ECons o env' => o ** environment_as_object env'
  end.

  Fixpoint environment_objects_as_list {n} (env: environment n): list object :=
  match env with
  | ENil => []
  | ECons o env' => o :: environment_objects_as_list env'
  end.

  (* Creates a right imbalanced tree of hetrogenous morphisms. Morphism
  * instances can then be recovered from the structure with the help of the
  * functions below *)
  Fixpoint env_morphisms (env_obj: object) (env_objs: list object): Type :=
  match env_objs with
  | [] => Datatypes.unit
  | ty::tys => prod (morphism env_obj ty) (env_morphisms env_obj tys)
  end.

  Fixpoint lookup_object (n: nat) (env: list object): option object :=
  match env with
  | [] => None
  | o :: os =>
    if eq_nat_dec n (length os)
    then Some o
    else lookup_object n os
  end.

  (* Shorthand for passing evidence that a lookup is well formed *)
  Notation ok_lookup := (
    fun (n: nat) (env: list object) (o: object) => lookup_object n env = Some o
  ).

  (* The type of a morphism in our environment is a morphism from our environment to the
  * object type at the index n, i.e. env_obj ~> o, where lookup_object n = Some o *)
  Fixpoint lookup_morphism_ty (n: nat) (env_obj: object) (objs: list object): Type :=
  match objs with
  | [] => Datatypes.unit
  | o::os =>
    if eq_nat_dec n (length os)
    then morphism env_obj o
    else lookup_morphism_ty n env_obj os
  end.

  (* Now we have the morphism type, we can pull a morphism out of the
  * hetrogenous env_obj which contains all the morphisms. *)
  Definition lookup_morphism (env_obj: object) (objs: list object):
    forall (n: nat), env_morphisms env_obj objs -> lookup_morphism_ty n env_obj objs.
  Proof.
    induction objs;
    intros.

    - exact tt.

    - simpl.
      destruct (eq_nat_dec n (length objs)).
      * exact (fst X).

      * apply IHobjs.
        exact (snd X).
  Defined.

  (* Proof that looking up a morphism is the morphism from the environment to
    * the object at the same index.
    *)
  Theorem ok_lookup_sets_lookup_morphism_ty : forall n o objs env_obj,
    lookup_object n objs = Some o
    -> lookup_morphism_ty n env_obj objs = morphism env_obj o.
  Proof.
    induction objs;
    intros.

    - simpl in H. easy.

    - simpl in *.
      destruct (eq_nat_dec n (length objs)); inversion H; auto.
  Defined.

  Definition morphism_coerce:
    forall (n:nat) env_obj o (objs: list object),
    ok_lookup n objs o ->
    lookup_morphism_ty n env_obj objs -> morphism env_obj o.
  Proof.
    intros.
    apply ok_lookup_sets_lookup_morphism_ty with (env_obj:=env_obj) in H.
    rewrite H in X.
    apply X.
  Defined.

  (* Map over the environment object. This is split into two functions to ease typing as
  prefixing the existing morphisms means they are not equal to recreating the
  morphism from the 'environment' they were created with, as the env_obj now
  contains 'ECons' levels from above. *)
  Definition contravariant_map'
    (env_obj env_obj': object)
    (objs: list object)
    (map: env_morphisms env_obj objs -> env_morphisms env_obj' objs)
    (f: env_obj' ~> env_obj)
    a
    (xs: (env_obj ~> a) * env_morphisms env_obj objs )
    : (env_obj' ~> a) * env_morphisms env_obj' objs :=
  match xs with
  | pair x xs => pair (f >>> x) (map xs)
  end.

  (* Map over the environment object *)
  Definition contra_map_morphisms
    (env_obj env_obj': object)
    (objs: list object)
    (morphs: env_morphisms env_obj objs)
    (f: env_obj' ~> env_obj)
    : env_morphisms env_obj' objs.
  Proof.
    induction objs.
    - exact tt.
    - simpl in *. auto.
      apply (contravariant_map' env_obj env_obj' objs IHobjs f).
      auto.
  Defined.

  (* Build the morphisms of an evnironment by using the arrow methods 'exl' and
  'exr' to extract eachs morphisms associated object from the environment object. *)
  Definition build_morphisms (n: nat) (env: environment n):
    env_morphisms (environment_as_object env) (environment_objects_as_list env).
  Proof.
    induction env; simpl.

    - apply (contra_map_morphisms
      (environment_as_object env)
      (environment_as_object (ECons o env))
      (environment_objects_as_list env )
      ) in IHenv.
      * intros.
        exact (pair exl IHenv).
      * exact exr.
    - exact tt.
  Defined.

  Lemma env_length_is_n  (n: nat) (env: environment n):
    length (environment_objects_as_list env) = n.
  Proof.
    induction env; simpl; auto.
  Defined.

  Lemma lookup_bound:
    forall n o objs,
    lookup_object n objs = Some o
    -> n < length objs.
  Proof.
    induction objs; intros.

    - inversion H.

    - simpl in H.
      destruct (Nat.eq_dec n (length objs)) as [n_eq | n_neq]; subst; auto.

      rewrite H in IHobjs.
      assert (Some o = Some o ).
      auto.
      apply IHobjs in H0.
      simpl.
      auto.
  Defined.

  Lemma lookup_bound_contra : forall o objs,
    lookup_object (length objs) objs = Some o
    -> False.
  Proof.
    intros.
    apply lookup_bound in H.
    apply Nat.lt_irrefl in H.
    inversion H.
  Defined.

  Lemma push_lookup: forall n objs o a,
    n < length objs
    -> lookup_object n (a::objs) = Some o
    -> lookup_object n objs = Some o.
  Proof.
    intros.
    case_eq (Nat.eq_dec n (length (objs))); intros.
    - rewrite e in H.
      apply Nat.lt_irrefl in H.
      contradiction.
    - simpl in H0.
      rewrite H1 in H0.
      apply H0.
  Defined.

  Lemma split_lookup : forall n env v1 y o,
    (v1 = n /\ y = o) \/ lookup_object v1 (environment_objects_as_list env) = Some o
    -> lookup_object v1 (environment_objects_as_list (@ECons n y env)) = Some o.
  Proof.
    intros.
    simpl.
    destruct (Nat.eq_dec v1 (length (environment_objects_as_list env))) as [n_eq | n_neq].
    - inversion H.
      * inversion H0.
        f_equal. auto.
      * rewrite n_eq in H0.
        apply lookup_bound_contra in H0.
        contradiction.
    - inversion H; auto.
      * inversion H0.
        rewrite H1 in n_neq.
        rewrite env_length_is_n in n_neq.
        destruct n_neq.
        auto.
  Defined.

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
  | DVar x            => ok_lookup x (environment_objects_as_list env) o
  | @DAbs _ _ x y z f => wf_debrujin (@ECons n x env) (f n)
  | DApp e1 e2        => wf_debrujin env e1 /\ wf_debrujin env e2
  | DCompose e1 e2    => wf_debrujin env e1 /\ wf_debrujin env e2
  | DArr _            => True
  end.

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
    (morphs: env_morphisms (environment_as_object env) (environment_objects_as_list env))
    (expr: kappa natvar i o) {struct expr}
    : wf_debrujin env expr -> morphism (i ** environment_as_object env) o :=
  match expr with
    (* Instantiating a variable is done by 'exr' to select the environment, and
    then indexing using lookup_morphism. 'morphisms_coerce' and 'wf' are used to
    align the types and to prove to Coq that the lookup is well formed. *)
  | DVar v => fun wf => exr >>> morphism_coerce _ wf (lookup_morphism (environment_as_object env) (environment_objects_as_list env) v morphs)
    (* Kappa abstraction requires extending the environment which includes
    modifying all the variable morphisms in scope (and their types!).
    *)
  | @DAbs _ _ x y z f => fun wf =>
    let env' := ECons x env in
    let f' := closure_conversion env' (build_morphisms env') (f n) wf in
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
    >>> closure_conversion env morphs e (proj2 wf)))
    >>> unassoc >>> first swap
    >>> closure_conversion env morphs f (proj1 wf)

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
    >>> first (closure_conversion env morphs e2 (proj2 wf))
    >>> closure_conversion env morphs e1 (proj1 wf)

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
    | Var_equiv : forall x y v1 v2 E,
      In (vars (obj_pair x y) (v1,v2)) E
      -> kappa_equivalence E (DVar v1) (DVar v2)

    | Abs_equiv : forall y (f1: var1 unit y -> kappa var1 unit y) f2 (E:ctxt),
      (forall v1 v2, kappa_equivalence (vars (obj_pair unit y) (v1,v2) :: E) (f1 v1) (f2 v2))
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

  (* Recovering a dependent value requires gentle proof steps (?) to prevent the
  equality disappearing. *)
  Lemma recover_dependent_val: forall y n xi o v1 v2,
    vars natvar natvar (obj_pair unit y) (n, n) = vars natvar natvar (obj_pair xi o) (v1, v2)
    -> n = v1.
  Proof.
    intros.
    inversion H.
    subst.
    generalize (inj_pairT2 _ _ _ _ _ H).
    intro.
    inversion H0.
    auto.
  Defined.

  Lemma found_at: forall n (env: environment n) v1 v2 o y xi,
    vars natvar natvar (obj_pair unit y) (n, n) = vars natvar natvar (obj_pair xi o) (v1, v2)
    -> (v1 = n /\ y = o).
  Proof.
    intros.
    split.
    apply recover_dependent_val in H.
    auto.
    inversion H.
    auto.
  Defined.

  (* Evidence that a variable is in an environment at an index implies a given
  object at a lookup_object index. *)
  Notation lookup_in_vars := (fun env E =>
    forall (xi xo : object) (v1 v2 : natvar xi xo),
      In (vars natvar natvar (obj_pair xi xo) (v1, v2)) E
      -> lookup_object v1 (environment_objects_as_list env) = Some xo
  ).

  Lemma lookup_in_extended_environment': forall n (env: environment n) v1 v2 xi xo y E,
    lookup_in_vars env E
    -> vars natvar natvar (obj_pair unit y) (n, n) = vars natvar natvar (obj_pair xi xo) (v1, v2) \/ lookup_object v1 (environment_objects_as_list env) = Some xo
    -> lookup_object v1 (environment_objects_as_list (ECons y env)) = Some xo.
  Proof.
    intros.
    rewrite split_lookup with (o:=xo); auto.
    inversion H0.
    - left.
      apply found_at with (v2:=v2) (xi:=xi); auto.
    - right.
      apply H1.
  Defined.

  Lemma lookup_in_extended_environment: forall n env v1 v2 y i o E,
    lookup_in_vars env E
    -> vars natvar natvar (obj_pair unit y) (n, n) = vars natvar natvar (obj_pair i o) (v1, v2) \/ In (vars natvar natvar (obj_pair i o) (v1, v2)) E
    -> lookup_object v1 (environment_objects_as_list (@ECons n y env)) = Some o.
  Proof.
    intros.

    eapply (lookup_in_extended_environment' H).

    inversion H0.
    - left. apply H1.
    - right. apply H with (xi:=i) (v2:=v2). apply H1.
  Defined.

  (* Apply the auto generated kappa_equivalence_ind induction scheme rather than
  calling induction directly as calling induction directly results in too
  specific hypotheses. *)
  Lemma kappa_wf
    : forall i o E (expr1 expr2: kappa natvar i o),
    kappa_equivalence E expr1 expr2
    -> forall n (env: environment n), lookup_in_vars env E
    -> wf_debrujin env expr1.

    apply (kappa_equivalence_ind
    (fun i o E (expr1 expr2 : kappa natvar i o) =>
      forall n (env: environment n),
        (forall xi xo (v1 v2 : natvar xi xo), In (vars _ _ (obj_pair xi xo) (v1, v2)) E
          -> lookup_object v1 (environment_objects_as_list env) = Some xo)
        -> wf_debrujin env expr1)
        ); intros; simpl in *; auto.

    - apply H0 in H. apply H.
    - apply H0 with (v2:=n).
      intros.
      apply lookup_in_extended_environment with (env:=env) in H2.
      apply H2.
      auto.
  Defined.

  Theorem Kappa_wf: forall {i o} (expr: forall var, kappa var i o), @wf_debrujin _ _ 0 ENil (expr _).
  Proof.
    intros.
    eapply kappa_wf.
    eapply Kappa_equivalence.
    intros.
    inversion H.
  Defined.

End WithArrow.

Definition Closure_conversion {arr i o} (expr: @Kappa arr i o): i ~> o
  := uncancelr >>> closure_conversion (ENil arr) tt (expr _) (Kappa_wf expr).
