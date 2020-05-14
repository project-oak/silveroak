From Coq Require Import Bool.Bvector.
From Coq Require Import Bool.Bool.
From Coq Require Import Setoid.
From Coq Require Import Classes.Morphisms.

From Cava Require Import Netlist.

Reserved Infix "~>" (at level 90, no associativity).
Reserved Infix "~[ C ]~>" (at level 90, no associativity).
Reserved Infix ">>>" (at level 53, right associativity).
Reserved Infix "=M=" (at level 54, no associativity).
Reserved Infix "~O~" (at level 54, no associativity).

Reserved Infix "**" (at level 30, right associativity).

(* more flexible than a haskell style category,
  which has morphisms between objects of type Hask.
  Here we have morphisms between objects of type object.
*)
Class Category := {
  object : Type;

  morphism : object -> object -> Type
    where "a ~> b" := (morphism a b);

  id {x} : x ~> x;

  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "g >>> f" := (compose f g);

  (* Setoid equivalence *)

  morphism_equivalence: forall x y (f g: x ~> y), Prop
    where "f =M= g" := (morphism_equivalence _ _ f g);
  morphism_setoid_equivalence : forall x y , Equivalence (morphism_equivalence x y);
  compose_respects_equivalence : forall x y z , Proper (morphism_equivalence y z ==> morphism_equivalence x y ==> morphism_equivalence x z) compose;

  (* Laws, used in rewriting *)

  id_left {x y} (f: x ~> y) : (id >>> f) =M= f;
  id_right {x y} (f: x ~> y) : (f >>> id) =M= f;

  associativity {x y z w} {f: x~>y} {g: y~>z} {h: z~>w} : (f >>> g) >>> h =M= f >>> (g >>> h);
}.

Declare Scope category_scope.
Bind Scope category_scope with Category.
Delimit Scope category_scope with category.

Notation "x ~> y" := (morphism x y) : category_scope.
Notation "x ~[ C ]~> y" := (@morphism C x y) (at level 90): category_scope.
Notation "g >>> f" := (compose f g) : category_scope.
Notation "f =M= g" := (morphism_equivalence _ _ f g) : category_scope.
(* Notation "x ~O~ y" := (object_equivalence x y) : category_scope. *)

Open Scope category_scope.

Add Parametric Relation (C: Category) (x y: object): (morphism x y) (morphism_equivalence x y)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (morphism_setoid_equivalence x y))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (morphism_setoid_equivalence x y))
  transitivity proved by (@Equivalence_Transitive _ _ (morphism_setoid_equivalence x y))
  as parametric_relation_eqv.

Hint Extern 1 => apply compose_respects_equivalence: core.
Hint Extern 1 => apply id_left: core.
Hint Extern 1 => apply id_right: core.

Add Parametric Morphism (C: Category) (x y z: object) : (@compose C x y z)
  with signature (morphism_equivalence _ _ ==> morphism_equivalence _ _ ==> morphism_equivalence _ _) 
  as parametric_morphism_comp.
Proof. auto. Defined.

(* This is the same as passing a pair type to 'sig', but is more convinent to use. *)
Inductive sig_pair (A B:Type) (P:A -> B -> Prop) : Type :=
  exist_pair : forall (x:A) (y:B), P x y -> sig_pair A B P.

(* adam megacz style arrow;
  There is no method to provide lifting a Coq function in general,
  although a particular arrow implementation may allow it.
*)
Class Arrow := {
  cat :> Category;
  unit : object;
  product : object -> object -> object
    where "x ** y" := (product x y);

  copy {x} : x ~> x**x;
  drop {x} : x ~> unit;
  swap {x y} : x**y ~> y**x;

  first {x y z} (f : x ~> y) : x ** z ~> y ** z;
  second {x y z} (f : x ~> y) : z ** x ~> z ** y;

  exl  {x y} : x ** y ~> x;
  exr  {x y} : x ** y ~> y;

  uncancell {x} : x ~> unit**x;
  uncancelr {x} : x ~> x**unit;
  assoc {x y z} : ((x**y)**z) ~> (x**(y**z));
  unassoc {x y z} : (x**(y**z)) ~> ((x**y)**z);

  (* laws, currently somewhat ad-hoc*)

  obj_equiv x y := 
    (sig_pair (x~>y) (y~>x) (fun f g => 
    f >>> g =M= id /\
    g >>> f =M= id
    ));

  exl_unit_uncancelr x : @exl x unit >>> uncancelr =M= id;
  exr_unit_uncancell x : @exr unit x >>> uncancell =M= id;
  uncancelr_exl x : uncancelr >>> @exl x unit =M= id;
  uncancell_exr x : uncancell >>> @exr unit x =M= id;

  drop_annhilates : forall x y (f: x~>y), f >>> drop =M= drop;
  exl_unit_is_drop : forall x, @exl unit x =M= drop;
  exr_unit_is_drop : forall x, @exr x unit =M= drop;

  exl_unit x : obj_equiv (x**unit) x;
  prefix_equiv x y : obj_equiv x y -> forall a, obj_equiv (a**x) (a**y);
}.

Coercion cat: Arrow >-> Category.

Declare Scope arrow_scope.
Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (product x y)
  (at level 30, right associativity) : arrow_scope.

Open Scope arrow_scope.

Definition apply_object_equivalence_left: forall (arr:Arrow) x y (H: obj_equiv x y), x~>y.
Proof.
  intros.
  inversion H.
  exact x0.
Defined.

Definition apply_object_equivalence_right: forall (arr:Arrow) x y (H: obj_equiv x y), y~>x.
Proof.
  intros.
  inversion H.
  exact y0.
Defined.

Ltac resolve_object_equivalence :=
  try repeat refine (prefix_equiv _ _ _ _);
  exact (exl_unit _).

(* Loop as a different type class to allow implementating a subset of features *)
Class ArrowLoop (A: Arrow) := {
  loopr {x y z} : (x**z ~> y**z) -> (x ~> y);
  loopl {x y z} : (z**x ~> z**y) -> (x ~> y);
}.

(* Cava *)
Class Cava  := {
  cava_arrow :> Arrow;

  bit : object;
  bitvec : nat -> object;

  constant : bool -> (unit ~> bit);
  constant_vec (n:nat) : Bvector n -> (unit ~> bitvec n);

  not_gate:  bit        ~> bit;
  and_gate:  bit ** bit ~> bit;
  nand_gate: bit ** bit ~> bit;
  or_gate:   bit ** bit ~> bit;
  nor_gate:  bit ** bit ~> bit;
  xor_gate:  bit ** bit ~> bit;
  xnor_gate: bit ** bit ~> bit;
  buf_gate:  bit        ~> bit;

  xorcy:     bit ** bit ~> bit;
  muxcy:     bit ** (bit ** bit) ~> bit;

  unsigned_add a b s: bitvec a ** bitvec b ~> bitvec s;
}.

Coercion cava_arrow: Cava >-> Arrow.

Definition cava_cat (_: Cava): Category := _.
Definition cava_obj (cava: Cava): Type := @object (@cava_cat cava).

Definition high {_: Cava}: unit ~> bit := constant true.
Definition low {_: Cava}: unit ~> bit := constant false.

(* Delay as a different type class to allow implementing subset of primitives *)
Class CavaDelay := {
  delay_cava :> Cava;
  delay_gate {x} : x ~> x;
}.

Coercion delay_cava: CavaDelay >-> Cava.

Definition cava_delay_arr (_: CavaDelay): Arrow := _.
