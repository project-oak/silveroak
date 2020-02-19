(* Require Coq.Program.Tactics. *)

Set Implicit Arguments.
Set Strict Implicit.

(* Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations. *)


Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "**" (at level 40, left associativity).
Reserved Infix ">>>" (at level 90, right associativity).

Section Theory.

(** haskell style category *)
Class Category := {
  morphism : Type -> Type -> Type
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
Context `{C : Category}.

Class Cartesian := {
  product : Type -> Type -> Type
    where "x ** y" := (product x y);

  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y ** z;
  exl  {x y} : x ** y ~> x;
  exr  {x y} : x ** y ~> y;
}.

Bind Scope cartesian_scope with Cartesian.
Delimit Scope cartesian_scope with cartesian.

Notation "x ** y" := (product x y)
  (at level 40, left associativity) : cartesian_scope.
  
Open Scope cartesian_scope.
Context `{CC : Cartesian}.

Definition first {x y z} (f : x ~> y) : x ** z ~> y ** z :=
  fork (exl >>> f) exr.

Definition second {x y z} (f : x ~> y) : z ** x ~> z ** y :=
  fork exl (exr >>> f).

(** adam megacz style arrow 
*)
Class Arrow := {
  unit : Type;

  uncancell {x} : x ~> (unit**x);
  uncancelr {x} : x ~> (x**unit);
  assoc {x y z} : ((x**y)**z) ~> (x**(y**z));
  unassoc {x y z} : (x**(y**z)) ~> ((x**y)**z);
  copy {x} : x ~> (x**x);
  drop {x} : x ~> unit;
  swap {x y} : (x**y) ~> (y**x);

  (** *)
  (* loopr {x y z} : ((x**z) ~> (y**z)) -> (x ~> y);
  loopl {x y z} : ((z**x) ~> (z**y)) -> (x ~> y); *)
}.

Print Arrow.
Context `{A : Arrow}.

Notation Bit := bool.
(** Cava *)
Class Cava := {
  delay_gate : Bit ~> Bit;
  not_gate : Bit ~> Bit;

  (** *)
  and_gate : (Bit ** Bit) ~> Bit;
}.

Print Cava.
Context `{@Cava}.

Definition nand := and_gate >>> not_gate.
Definition xor : (Bit**Bit) ~> Bit := 
  copy 
  >>> first (nand >>> copy)      (* ((nand,nand),(x,y)) *)
  >>> assoc                      (* (nand,(nand,(x,y))) *)
  >>> second (unassoc >>> first nand >>> swap) (* (nand,(y, x_nand)) *)
  >>> unassoc >>> first nand          (* (y_nand,x_nand) *)
  >>> nand.

(*nand previous output and current input, output delayed 1 cycle*)
(* Definition loopedNand : Bit ~> Bit := 
  loopl (nand >>> delay_gate >>> copy). *)

End Theory.

Section NaiveEval.

Section Example.
  Instance Coq : Category := {
    morphism := fun x y => x -> y;
    id  := fun _ x => x;
    compose := fun _ _ _ f g => (fun x => f (g x))
  }.

  Print Coq.

  Instance CoqC : @Cartesian Coq := {
    product x y := prod x y;
    fork := fun _ _ _ f g => (fun x => (f x, g x));
    exl := fun _ _ x => fst x;
    exr := fun _ _ x => snd x;
  }.

  (* Coercion prod_is_tuple () : prod x y := (product @CoqC x y).  *)

  Print CoqC.

  Print Arrow.


  Instance CoqA : @Arrow Coq CoqC := {
    unit := Datatypes.unit;

    drop := fun _ => fun _ => tt; 
    copy := fun _ => fun x => (x,x); 
    swap := fun _ _ => fun xy => (snd xy, fst xy);

    uncancelr := fun _ => fun x => (x,tt);
    uncancell := fun _ => fun x => (tt,x);

    assoc := fun _ _ _ => fun xyz => (fst (fst xyz), (snd (fst xyz), snd xyz));
    unassoc := fun _ _ _ => fun xyz => ((fst xyz, fst (snd xyz)), snd (snd xyz));

    (** *)
    (* loopr {x y z} : ((x**z) ~> (y**z)) -> (x ~> y);
    loopl {x y z} : ((z**x) ~> (z**y)) -> (x ~> y); *) 
  }.


End NaiveEval.