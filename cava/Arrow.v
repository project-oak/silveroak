Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

From Coq Require Import btauto.Btauto.

Set Implicit Arguments.
Set Strict Implicit.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Set Typeclasses Debug.
Set Typeclasses Debug Verbosity 2.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "**" (at level 40, left associativity).
Reserved Infix ">>>" (at level 90, right associativity).

(** haskell-ish style category
*)
Class Category := {
  object : Type;

  morphism : object -> object -> Type
    where "a ~> b" := (morphism a b);

  id {x} : x ~> x;

  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "g >>> f" := (compose f g);
}.

Bind Scope category_scope with Category.
Delimit Scope category_scope with category.

Notation "x ~> y" := (morphism x y)
  (at level 90, right associativity) : category_scope.
Notation "g >>> f" := (compose f g)
  (at level 90, right associativity) : category_scope.



Open Scope category_scope.
Print Category.

(** adam megacz style arrow *)
Class Arrow := {
  cat :> Category; 
  unit : object;
  product : object -> object -> object
    where "x ** y" := (product x y);

  copy {x} : x ~> (x**x);
  drop {x} : x ~> unit;
  swap {x y} : (x**y) ~> (y**x);

  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y ** z;
  exl  {x y} : x ** y ~> x;
  exr  {x y} : x ** y ~> y;

  uncancell {x} : x ~> (unit**x);
  uncancelr {x} : x ~> (x**unit);
  assoc {x y z} : ((x**y)**z) ~> (x**(y**z));
  unassoc {x y z} : (x**(y**z)) ~> ((x**y)**z);
}.

Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (product x y)
  (at level 40, left associativity) : arrow_scope.

Open Scope arrow_scope.

Definition first `{Arrow} {x y z} (f : x ~> y) : x ** z ~> y ** z :=
  fork (exl >>> f) exr.

Definition second `{Arrow} {x y z} (f : x ~> y) : z ** x ~> z ** y :=
  fork exl (exr >>> f).

(** different type class for implementation to select features*)
(* Class ArrowLoop {C: Category} (A: Arrow C) := { *)
Class ArrowLoop := {
  arr :> Arrow;
  loopr {x y z} : ((x**z) ~> (y**z)) -> (x ~> y);
  loopl {x y z} : ((z**x) ~> (z**y)) -> (x ~> y);
}.

Print Arrow.

(** Cava *)
Class Cava  := {
  cava_arrow :> Arrow;
  bit : object;

  (* fromBool : bool -> (unit ~> bit); *)

  not_gate : bit ~> bit;
  and_gate : (bit ** bit) ~> bit;
}.

Definition cava_cat (cava: Cava): Category := @cat (@cava_arrow cava).
Definition cava_obj (cava: Cava): Type := @object (@cava_cat cava).

(* Section highlow.
  Context `{Cava}.
  Definition high : unit ~> bit := fromBool true.
  Definition low : unit ~> bit := fromBool false.
End highlow. *)

(** different type class for implementation to select features*)
Class CavaDelay `{Cava} := {
  delay_gate : bit ~> bit;
}.

Print Cava.

(** Evaluation as function, no delay elements or loops *)
Section CoqEval.
  Instance CoqCat : Category := {
    morphism X Y := X -> Y;
    compose _ _ _ := fun f g x => f (g x);
    id X := fun x => x;
  }.

  Instance CoqArr : Arrow := {
    unit := Datatypes.unit : Type;
    product := prod;

    fork _ _ _ f g := fun x => (f x, g x);
    exl X Y := fst;
    exr X Y := snd;

    drop _ := fun x => tt;
    copy _ := fun x => pair x x;

    swap _ _ := fun x => (snd x, fst x);

    uncancell _ := fun x => (tt, x);
    uncancelr _ := fun x => (x, tt);

    assoc _ _ _   := fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz));
    unassoc _ _ _ := fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz));
  }.

  Instance CoqCava : Cava := {
    bit := bool;

    (* fromBool b := fun _ => b; *)

    not_gate := fun b => negb b;
    and_gate := fun xy => andb (fst xy) (snd xy);
  }.

  Definition eval {A B} (f: A~>B) (a:A): B := f a.
  Definition eval' {B} (f: unit~>B) : B := f tt.

  Context `{CavaCoq}.
  Eval cbv in eval not_gate true.
  Eval cbv in eval not_gate false.
End CoqEval.

(** Evaluation as function on lists, no loops *)
Section CoqListEval.
  Instance CoqListCat : Category := {
    morphism X Y := list X -> list Y;
    compose _ _ _ := fun f g x => f (g x);
    id X := fun x => x;
  }.

  Instance CoqListArr : Arrow := {
    unit := Datatypes.unit : Type;

    fork _ _ _ f g := fun xs => combine (f xs) (g xs);
    exl X Y := map fst;
    exr X Y := map snd;

    drop _ := map (fun _ => tt);
    copy _ := map (fun x => pair x x);

    swap _ _ := map (fun x => (snd x, fst x));

    uncancell _ := map (fun x => (tt, x));
    uncancelr _ := map (fun x => (x, tt));

    assoc _ _ _   := map (fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz)));
    unassoc _ _ _ := map (fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz)));
  }.

  Instance CoqListCava : Cava := {
    bit := bool;

    (* fromBool b := fun _ => b; *)

    not_gate := map (fun b => negb b);
    and_gate := map (fun xy => andb (fst xy) (snd xy));
  }.
   
  Definition evalList (A: @object CoqListCat) (B: @object CoqListCat) (f: @morphism CoqListCat A B) (a:list A): list B := f a.

  Import ListNotations.

  Eval cbv in evalList not_gate [true;true;true].
  Eval cbv in evalList not_gate [false;false;false].
End CoqListEval.


Section Example1.
  Definition nand
    {Cava: Cava}
    := and_gate >>> not_gate.

  Definition xor
    {_: Cava}
    : (bit**bit) ~> bit :=
    copy
    >>> first (nand >>> copy)                    (* ((nand,nand),(x,y)) *)
    >>> assoc                                    (* (nand,(nand,(x,y))) *)
    >>> second (unassoc >>> first nand >>> swap) (* (nand,(y, x_nand)) *)
    >>> unassoc >>> first nand                   (* (y_nand,x_nand) *)
    >>> nand.

  (* Definition twoBits
    {C: Category} {A: Arrow C}
    {Cava: @Cava C A}
    : unit ~> (bit**bit) :=
    copy
    >>> first (fromBool true)
    >>> second (fromBool false).

  Existing Instance CoqArr.
  Existing Instance CoqCava.

  Print xor.
  Eval simpl in eval' (twoBits >>> and_gate).
  Eval cbv in eval' (twoBits >>> and_gate).
  Eval simpl in eval' (twoBits >>> nand).
  Eval cbv in eval' (twoBits >>> nand).
  Eval simpl in eval' (twoBits >>> xor).
  Eval cbv in eval' (twoBits >>> xor).

  Definition twoBools
    {C: Category} {A: Arrow C}
    {Cava: @Cava C A}
    (x y: bool): unit ~> (bit**bit) :=
    copy
    >>> first (fromBool x)
    >>> second (fromBool y). *) 

  (** *)
  Print eval.

  Lemma xor_is_xorb: forall a b:bool, eval (@xor CoqCava) (pair a b) = xorb a b.
  Proof.
    intros.
    unfold eval.
    unfold xor.
    unfold nand.
    simpl.
    btauto.
  Qed.

  Definition nandb : bool -> bool -> bool := fun a b => negb (a && b).
  Definition uncurry {a b c} (f: a -> b -> c) : (a*b) -> c := fun xy => f (fst xy) (snd xy).

  Lemma nand_is_comb: forall a:list (bool*bool), evalList (@nand CoqListCava) a = map (uncurry nandb) a.
  Proof.
    intros.
    unfold nand.
    unfold evalList.
    simpl.
    rewrite map_map.
    constructor.
  Qed.

  Lemma xor_comb: forall a:list (bool*bool), evalList (@xor CoqListCava) a = map (uncurry xorb) a.
  Proof.
    intros.
    induction a.
    simpl.
    reflexivity.

    cbv [evalList xor uncurry nand].
    simpl.
    f_equal.
    btauto.

    cbv [evalList xor uncurry nand] in IHa.
    simpl in IHa.
    rewrite IHa.
    reflexivity.
  Qed.

End Example1.

Section Example2.
  (*nand previous output and current input, output delayed 1 cycle*)
  Definition loopedNand
    {C: Category}
    {A: Arrow C} {AL: ArrowLoop A}
    {Cava: @Cava C A}
    `{@CavaDelay C A Cava}
    : bit ~> bit :=
    loopl (nand >>> delay_gate >>> copy).
End Example2.

Section Syntax.
  Context `{C: Category}.

  Inductive type : Type :=
  | obj (o: object) : type
  | fn: type -> type -> type.

  Variable var: type -> Type.

  Inductive lambda : type -> Type :=
  | Var : forall t, var t -> lambda t
  | Abs : forall x y, (var x -> lambda y) -> lambda (fn x y)
  | App : forall x y, lambda (fn x y) -> lambda x -> lambda y
  | Arr x y (_: morphism x y) : lambda (fn (obj x) (obj y))
  (* TODO: | Let ... *)
  (* TODO: | LetRec ... *)
  .

  Inductive typeK : Type :=
  | objK (o: object)
  | prodK (o1: typeK) (o2: typeK)
  | unitK.

  Variable varK: typeK -> typeK -> Type.

  Inductive kappa : typeK -> typeK -> Type :=
  | VarK : forall x y, varK x y -> kappa x y
  | IdK : forall x, kappa x x
  | FirstK : forall x y z, kappa x y -> kappa (prodK x z) (prodK y z)
  | CompK : forall x y z, kappa y z -> kappa x y -> kappa x z
  | AbsK : forall x y z, (varK unitK x -> kappa (prodK x z) y) -> kappa (prodK x z) y.
End Syntax.

Section SanityCheck.

  Context {C: Category}.

  Arguments Var _ [var t] _.
  Arguments Abs _ [var x y] _.

  Definition Term t := forall var, lambda var t.

  Check Term.

  Definition Foo {x} : Term (fn x x) := fun _ => Abs _ (fun x => Var _ x).
  Definition Bar {x y} : Term (fn (fn y x) (fn y x))
  := fun _ =>
  Abs _ (fun x => 
      Abs _ (fun y =>
        App (Var _ x) (Var _ y)
      )
    ).
  Definition Baz {a b} (arr: a~>b): Term (fn (obj a) (obj b))
  := fun _ => Abs _ (fun x => App (Arr _ _ _ arr) (Var _ x)).


  Fixpoint squash var t (e : lambda (lambda var) t) : lambda var t :=
  match e with
  | Var _ x => x
  | Abs _ e1 => Abs _ (fun v => squash(e1 (Var _ v)))
  | App e1 e2 => App (squash e1) (squash e2) 
  | Arr _ x y m => Arr _ x y m
  end.

  Definition Term1 (t1 t2 : type) := forall var, var t1 -> lambda var t2.
  Definition Subst (t1 t2 : type) (E : Term1 t1 t2 ) (E' : Term t1 ) : Term t2 :=
  fun var => squash (E (lambda var) (E' var)).




End SanityCheck.