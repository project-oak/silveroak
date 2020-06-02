From Coq Require Import Setoid Classes.Morphisms Lists.List NaryFunctions String.
Import ListNotations.

From Cava Require Import Types.

Reserved Infix "~>" (at level 90, no associativity).
Reserved Infix "~[ C ]~>" (at level 90, no associativity).
Reserved Infix ">>>" (at level 53, right associativity).
Reserved Infix "=M=" (at level 54, no associativity).

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

  first  {x y z} (f : x ~> y) : x ** z ~> y ** z;
  second {x y z} (f : x ~> y) : z ** x ~> z ** y;

  exl  {x y} : x ** y ~> x;
  exr  {x y} : x ** y ~> y;

  uncancell {x} : x ~> unit**x;
  uncancelr {x} : x ~> x**unit;
  assoc   {x y z} : ((x**y)**z) ~> (x**(y**z));
  unassoc {x y z} : (x**(y**z)) ~> ((x**y)**z);

  (* laws, currently somewhat ad-hoc*)

  exl_unit_uncancelr x: @exl x unit >>> uncancelr =M= id;
  exr_unit_uncancell x: @exr unit x >>> uncancell =M= id;
  uncancelr_exl x:      uncancelr >>> @exl x unit =M= id;
  uncancell_exr x:      uncancell >>> @exr unit x =M= id;

  drop_annhilates {x y} (f: x~>y): f >>> drop =M= drop;

  exl_unit_is_drop {x}: @exl unit x =M= drop;
  exr_unit_is_drop {x}: @exr x unit =M= drop;

  first_first   {x y z w} (f: x~>y) (g:y~>z): @first x y w f >>> first g  =M= first (f >>> g);
  second_second {x y z w} (f: x~>y) (g:y~>z): @second x y w f >>> second g  =M= second (f >>> g);

  swap_swap {x y}: @swap x y >>> swap =M= id;

  first_id  {x w}: @first x x w id  =M= id;
  second_id {x w}: @second x x w id  =M= id;

  first_f  {x y w} (f: x~>y) (g:x~>y): f =M= g -> @first x y w f =M= first g;
  second_f {x y w} (f: x~>y) (g:x~>y): f =M= g -> @second x y w f =M= second g;

  assoc_unassoc {x y z}: @assoc x y z >>> unassoc =M= id;
  unassoc_assoc {x y z}: @unassoc x y z >>> assoc =M= id;

  first_exl  {x y w} f: @first x y w f >>> exl =M= exl >>> f;
  second_exr {x y w} f: @second x y w f >>> exr =M= exr >>> f;
}.

Coercion cat: Arrow >-> Category.

Declare Scope arrow_scope.
Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (product x y)
  (at level 30, right associativity) : arrow_scope.

Open Scope arrow_scope.

(* Loop as a different type class to allow implementating a subset of features *)
Class ArrowLoop (A: Arrow) := {
  loopr {x y z} : (x**z ~> y**z) -> (x ~> y);
  loopl {x y z} : (z**x ~> z**y) -> (x ~> y);
}.

(*
replicate_object returns an object in the argument format expect by Kappa Calculus.
That is, the object is repeated n times, as a right nested tuple, with the rightmost
tuple element set to the unit type.
*)
Fixpoint replicate_object `{Arrow} (n: nat) (o: object) :=
match n with 
| O => unit
| S n' => o ** replicate_object n' o 
end.

Reserved Notation "'bit'" (at level 1, no associativity).
Reserved Notation "'bitvec' n" (at level 1, no associativity).
Reserved Notation "'bitvec_index' n" (at level 1, no associativity).

(* Cava *)
Class Cava  := {
  cava_arrow :> Arrow;

  representable : Kind -> object
    where "'bit'" := (representable Bit)
    and   "'bitvec' n" := (representable (BitVec n))
    and   "'bitvec_index' n" := (bitvec [PeanoNat.Nat.log2_up n]);

  constant : bool -> (unit ~> bit);
  constant_vec (dimensions: list nat) : denoteBitVecWith bool dimensions -> (unit ~> bitvec dimensions);

  not_gate:  bit        ** unit ~> bit;
  and_gate:  bit ** bit ** unit ~> bit;
  nand_gate: bit ** bit ** unit ~> bit;
  or_gate:   bit ** bit ** unit ~> bit;
  nor_gate:  bit ** bit ** unit ~> bit;
  xor_gate:  bit ** bit ** unit ~> bit;
  xnor_gate: bit ** bit ** unit ~> bit;
  buf_gate:  bit        ** unit ~> bit;

  xorcy:     bit ** bit ** unit ~> bit;
  muxcy:     bit ** (bit ** bit) ** unit ~> bit;
  
  unsigned_add a b c: bitvec [a] ** bitvec [b] ** unit ~> bitvec [c];

  lut n: (bool^^n --> bool) -> (replicate_object n bit) ~> bit;

  degenerate_bitvec xs := match xs with | [] => bit | _ => bitvec xs end;

  index_array n xs
    : bitvec (n::xs) ** bitvec_index n ** unit 
    ~> degenerate_bitvec xs;

  to_vec n o:
    match o with
    | Bit => replicate_object (S n) bit ~> bitvec [S n]
    | BitVec xs => replicate_object (S n) (bitvec xs) ~> bitvec (S n::xs)
    end;
}.

Coercion cava_arrow: Cava >-> Arrow.

Declare Scope cava_scope.
Bind Scope cava_scope with Cava.
Delimit Scope cava_scope with cava.

Notation "'bit'" := (representable Bit)(at level 1, no associativity) : cava_scope.
Notation "'bitvec' n" := (representable (BitVec n)) (at level 1, no associativity) : cava_scope.
Notation "'bitvec_index' n" := (bitvec [PeanoNat.Nat.log2_up n])%cava(at level 1, no associativity) : cava_scope.

Open Scope cava_scope.

Definition cava_cat (_: Cava): Category := _.
Definition cava_obj (cava: Cava): Type := @object (@cava_cat cava).

Definition high {_: Cava}: unit ~> bit := constant true.
Definition low {_: Cava}: unit ~> bit := constant false.

(* Delay as a different type class to allow implementing subset of primitives *)
Class CavaDelay := {
  delay_cava :> Cava;
  delay_gate {x} : x ** unit ~> x;
}.

Coercion delay_cava: CavaDelay >-> Cava.

Definition cava_delay_arr (_: CavaDelay): Arrow := _.

(* experimental equivalence rewriting functions *)
Lemma simpl_firsts
  {A: Arrow} {x y z w o}
  (f:x~>y) (g:y~>z) (h:z**w~>o): @first _ x y w f >>> (first g >>> h) =M= first (f >>> g) >>> h.
Proof.
  intros.
  setoid_rewrite <- associativity.
  setoid_rewrite first_first.
  reflexivity.
Qed.

Lemma simpl_seconds
  {A: Arrow} {x y z w o}
  (f:x~>y) (g:y~>z) (h:w**z~>o): @second _ x y w f >>> (second g >>> h) =M= second (f >>> g) >>> h.
Proof.
  intros.
  setoid_rewrite <- associativity.
  setoid_rewrite second_second.
  reflexivity.
Qed.

Lemma trans_apply
  {A: Arrow} {x y z w}
  (f:x~>y) (g:y~>z) (h:x~>z) (i: z~>w):
  f >>> g =M= h -> f >>> (g >>> i) =M= h >>> i.
Proof.
  intros.
  setoid_rewrite <- associativity.
  setoid_rewrite H.
  reflexivity.
Qed.
