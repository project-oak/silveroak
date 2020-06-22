From Coq Require Import Setoid Classes.Morphisms Lists.List NaryFunctions String Arith NArith VectorDef.
Import ListNotations.
Import VectorNotations.

From Cava Require Import Types.

Reserved Infix "~>" (at level 90, no associativity).
Reserved Infix "~[ C ]~>" (at level 90, no associativity).
Reserved Infix ">>>" (at level 53, right associativity).
Reserved Infix "=M=" (at level 54, no associativity).

Reserved Infix "**" (at level 30, right associativity).

Generalizable Variable object category unit product.
(* Generalizable Variable category. *)

(* more flexible than a haskell style category,
  which has morphisms between objects of type Hask.
  Here we have morphisms between objects of type object.
*)
Class Category (object: Type) := {
  (* object := obj; *)

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

(* Coercion object: Category >-> Sortclass. *)

Declare Scope category_scope.
Bind Scope category_scope with Category.
Delimit Scope category_scope with category.

Notation "x ~> y" := (morphism x y) : category_scope.
Notation "x ~[ C ]~> y" := (@morphism _ C x y) (at level 90): category_scope.
Notation "g >>> f" := (compose f g) : category_scope.
Notation "f =M= g" := (morphism_equivalence _ _ f g) : category_scope.

Open Scope category_scope.

Add Parametric Relation (object: Type) (C: Category object) (x y: object): (morphism x y) (morphism_equivalence x y)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (morphism_setoid_equivalence x y))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (morphism_setoid_equivalence x y))
  transitivity proved by (@Equivalence_Transitive _ _ (morphism_setoid_equivalence x y))
  as parametric_relation_eqv.

Hint Extern 1 => apply compose_respects_equivalence : core.
Hint Extern 1 => apply id_left : core.
Hint Extern 1 => apply id_right : core.

Add Parametric Morphism (object: Type) (C: Category object) (x y z: object) : (@compose object C x y z)
  with signature (morphism_equivalence _ _ ==> morphism_equivalence _ _ ==> morphism_equivalence _ _)
  as parametric_morphism_comp.
Proof. 
  auto.
Defined.

(* adam megacz style generalized arrow,
  laws coming from monoidal categories *)
Class Arrow (object: Set) `(C: Category object) (unit: object) (product: object -> object -> object) := {
  arrow_cat := C;
  u := unit;
  product := product
    where "x ** y" := (product x y);

  first  {x y z} (f: x ~> y) : x ** z ~> y ** z;
  second {x y z} (f: x ~> y) : z ** x ~> z ** y;

  bimap {x y z w} (f: x ~> y) (g: z ~> w) := first f >>> second g;

  assoc   {x y z} : ((x**y)**z) ~> (x**(y**z));
  unassoc {x y z} : (x**(y**z)) ~> ((x**y)**z);

  cancelr  {x} : x ** unit ~> x;
  cancell  {x} : unit ** x ~> x;

  uncancell {x} : x ~> unit**x;
  uncancelr {x} : x ~> x**unit;

  (* (un)cance{l,r} and (un)assoc are natural isomorphisms *)
  first_cancelr   {x y} (f: x ~> y): first f >>> cancelr =M= cancelr >>> f;
  uncancelr_first {x y} (f: x ~> y): uncancelr >>> first f =M= f >>> uncancelr;

  second_cancell   {x y} (f: x ~> y): second f >>> cancell =M= cancell >>> f;
  uncancell_second {x y} (f: x ~> y): uncancell >>> second f =M= f >>> uncancell;

  assoc_iso {x y z w s t} (f: x ~> y) (g: z ~> w) (h: s ~> t): 
    assoc >>> bimap _ _ _ _ f (bimap _ _ _ _ g h) =M= bimap _ _ _ _ (bimap _ _ _ _ f g) h >>> assoc;

  unassoc_iso {x y z w s t} (f: x ~> y) (g: z ~> w) (h: s ~> t): 
    unassoc >>> bimap _ _ _ _ (bimap _ _ _ _ f g) h =M= bimap _ _ _ _ f (bimap _ _ _ _ g h) >>> unassoc;

  (* triangle and pentagon identities? *)
}.

Coercion arrow_cat: Arrow >-> Category.

Declare Scope arrow_scope.
Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (product x y)
  (at level 30, right associativity) : arrow_scope.

Open Scope arrow_scope.

Class ArrowCopy `(A: Arrow) := {
  copy {x} : x ~> x**x;
}.

Class ArrowDrop `(A: Arrow) := {
  drop {x} : x ~> u;
}.

Class ArrowSwap `(A: Arrow) := {
  swap {x y} : x**y ~> y**x;
}.

Class ArrowLoop `(A: Arrow) := {
  loopr {x y z} : (x**z ~> y**z) -> (x ~> y);
  loopl {x y z} : (z**x ~> z**y) -> (x ~> y);
}.

(* TODO: uses these?
Class ArrowConstant (A: Arrow) (r: @object A) t := {
  constant : t -> unit ~> r;
}.

Class ArrowSum (Arrow (**) u, Arrow (<+>) v) := {
  merge : (x<+>x) ~> x;
  never : v ~> x;
}.

Class ArrowProd (Arrow (**) u, Arrow (<*>) v) := {
  prod_copy : g x (x<*>x)
  prod_drop : g x v
}. 
*)

(* Class CircuitLaws `(A: Arrow, ! ArrowCopy A, ! ArrowSwap A, ! ArrowDrop A) := {
  cancelr_unit_uncancelr {x}: @cancelr x >>> uncancelr =M= id;
  cancell_unit_uncancell {x}: @cancell _ _ A x >>> uncancell =M= id;
  uncancelr_cancelr {x}:      @uncancelr _ _ A x >>> cancelr =M= id;
  uncancell_cancell {x}:      @uncancell _ _ A x >>> cancell =M= id;

  drop_annhilates {x y} (f: x~>y): f >>> drop =M= drop;

  cancelr_unit_is_drop : @cancelr A unit =M= drop;
  cancell_unit_is_drop : @cancell A unit =M= drop;

  first_first   {x y z w} (f: x~>y) (g:y~>z): @first A x y w f >>> first g  =M= first (f >>> g);
  second_second {x y z w} (f: x~>y) (g:y~>z): @second A x y w f >>> second g  =M= second (f >>> g);

  swap_swap {x y}: @swap A _ x y >>> swap =M= id;

  first_id  {x w}: @first A x x w id  =M= id;
  second_id {x w}: @second A x x w id  =M= id;

  first_f  {x y w} (f: x~>y) (g:x~>y): f =M= g -> @first A x y w f =M= first g;
  second_f {x y w} (f: x~>y) (g:x~>y): f =M= g -> @second A x y w f =M= second g;
}. *)

Inductive Kind : Set :=
| Tuple: Kind -> Kind -> Kind
| Unit: Kind
| Bit: Kind
| Vector: nat -> Kind -> Kind.

Fixpoint decKind (k1 k2: Kind) {struct k1} : {k1=k2} + {k1<>k2}. 
Proof.
  decide equality.
  exact (PeanoNat.Nat.eq_dec n n0).
Defined.

Require Import Eqdep.

Lemma kind_eq: forall ty, decKind ty ty = left eq_refl.
Proof.
  intros. 
  destruct (decKind ty ty); try rewrite (UIP_refl _ _ _); auto.
  destruct n.
  reflexivity.
Qed.

Ltac reduce_kind_eq :=
  match goal with 
  | [ |- context[decKind _ _] ] =>
    rewrite kind_eq; unfold eq_rect_r, eq_rect, eq_sym
  | [H: context[decKind _ _] |- _] =>
    rewrite kind_eq in H; unfold eq_rect_r, eq_rect, eq_sym in H
  end; try subst.

Declare Scope kind_scope.
Bind Scope kind_scope with Kind.
Delimit Scope kind_scope with Kind.

Notation "<< x >>" := (x) : kind_scope.
Notation "<< x , .. , y , z >>" := (Tuple x .. (Tuple y z )  .. ) : kind_scope.

Fixpoint vec_to_nprod (A: Type) n (v: Vector.t A n): A^n :=
match v with
| [] => tt
| x::xs => (x, vec_to_nprod A _ xs)
end%vector.

(* log2_up is used for getting the necessary number of bits required to represent an index.
Currently some of the Arrow.Cava and Kappa parts take non-zero sized vectors, and so we require a 
minimum size of 1 for now. *)
Definition log2_up_min_1 (n: nat): nat :=
  match n with
  | 0 => 1 
  | 1 => 1 
  | S n => Nat.log2_up (S n)
  end.

(* Cava *)
Class Cava := {
  cava_cat :> Category Kind;
  cava_arrow :> Arrow Kind cava_cat Unit Tuple;
  cava_arrow_drop :> ArrowDrop _;
  cava_arrow_swap :> ArrowSwap _;
  cava_arrow_copy :> ArrowCopy _;
  cava_arrow_loop :> ArrowLoop _;

  vec_index n := Vector (log2_up_min_1 n) Bit;

  constant : bool -> (Unit ~> Bit);
  constant_bitvec n: N -> (Unit ~> Vector n Bit);

  not_gate:  Bit        ~> Bit;
  and_gate:  Bit ** Bit ~> Bit;
  nand_gate: Bit ** Bit ~> Bit;
  or_gate:   Bit ** Bit ~> Bit;
  nor_gate:  Bit ** Bit ~> Bit;
  xor_gate:  Bit ** Bit ~> Bit;
  xnor_gate: Bit ** Bit ~> Bit;
  buf_gate:  Bit        ~> Bit;

  delay_gate {o} : o ~> o;

  xorcy:     Bit ** Bit ~> Bit;
  muxcy:     Bit ** (Bit ** Bit) ~> Bit;
  
  unsigned_add a b c: Vector a Bit ** Vector b Bit ~> Vector c Bit;

  lut n: (bool^^n --> bool) -> Vector n Bit ~> Bit;

  index_vec n o: Vector n o ** vec_index n ~> o;
  (* slice [x:y] where x >= y, x is inclusive 
  So, slice_vec vec [1:0] is the bitvector [vec[0],vec[1]] : Vector 2 _ 
  *)
  slice_vec n x y o: x < n -> y <= x -> Vector n o ~> Vector (x - y + 1) o;
  to_vec o: o ~> Vector 1 o;
  append n o: Vector n o ** o ~> Vector (n+1) o;
  concat n m o: Vector n o ** Vector m o ~> Vector (n + m) o;
  split n m o: m < n -> Vector n o ~> (Vector m o ** Vector (n - m) o);
}.

Coercion cava_cat: Cava >-> Category.
Coercion cava_arrow: Cava >-> Arrow.
Coercion cava_arrow_swap: Cava >-> ArrowSwap.
Coercion cava_arrow_drop: Cava >-> ArrowDrop.
Coercion cava_arrow_copy: Cava >-> ArrowCopy.
Coercion cava_arrow_loop: Cava >-> ArrowLoop.

Declare Scope cava_scope.
Bind Scope cava_scope with Cava.
Delimit Scope cava_scope with cava.

Open Scope cava_scope.

Definition high {_: Cava}: Unit ~> Bit := constant true.
Definition low {_: Cava}: Unit ~> Bit := constant false.