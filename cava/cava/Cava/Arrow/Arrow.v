From Coq Require Import Setoid Classes.Morphisms Lists.List NaryFunctions String NArith.
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

(* adam megacz style generalized arrow,
  laws coming from monoidal categories *)
Class Arrow := {
  cat :> Category;
  unit : object;
  product : object -> object -> object
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

Coercion cat: Arrow >-> Category.

Declare Scope arrow_scope.
Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (product x y)
  (at level 30, right associativity) : arrow_scope.

Open Scope arrow_scope.

Class ArrowCopy (A: Arrow) := {
  copy {x} : x ~> x**x;
}.

Class ArrowDrop (A: Arrow) := {
  drop {x} : x ~> unit;
}.

Class ArrowSwap (A: Arrow) := {
  swap {x y} : x**y ~> y**x;
}.

Class ArrowLoop (A: Arrow) := {
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

Class CircuitLaws `(A: Arrow, ! ArrowCopy A, ! ArrowSwap A, ! ArrowDrop A) := {
  cancelr_unit_uncancelr {x}: @cancelr A x >>> uncancelr =M= id;
  cancell_unit_uncancell {x}: @cancell A x >>> uncancell =M= id;
  uncancelr_cancelr {x}:      @uncancelr A x >>> cancelr =M= id;
  uncancell_cancell {x}:      @uncancell A x >>> cancell =M= id;

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
}.

(* Cava *)
Class Cava  := {
  cava_arrow :> Arrow;
  cava_arrow_drop :> ArrowDrop _;
  cava_arrow_swap :> ArrowSwap _;
  cava_arrow_copy :> ArrowCopy _;
  cava_arrow_loop :> ArrowLoop _;
  (* Todo: blocked by combinational evaluator, which should be able to provide CircuitLaws
  but currently doesn't *)
  (* cava_circuit_laws :> CircuitLaws cava_arrow _ _ _; *)

  bit : object;
  vector (n: N) o: object;

  bitvec n := vector n bit;
  bitvec_index n := bitvec (N.log2_up n);

  constant : bool -> (unit ~> bit);
  constant_bitvec n: N -> (unit ~> bitvec n);

  not_gate:  bit        ~> bit;
  and_gate:  bit ** bit ~> bit;
  nand_gate: bit ** bit ~> bit;
  or_gate:   bit ** bit ~> bit;
  nor_gate:  bit ** bit ~> bit;
  xor_gate:  bit ** bit ~> bit;
  xnor_gate: bit ** bit ~> bit;
  buf_gate:  bit        ~> bit;

  delay_gate {o} : o ~> o;

  xorcy:     bit ** bit ~> bit;
  muxcy:     bit ** (bit ** bit) ~> bit;
  
  unsigned_add a b c: bitvec a ** bitvec b ~> bitvec c;

  lut n: (bool^^n --> bool) -> bitvec (N.of_nat n) ~> bit;

  index_vec n o: vector n o ** bitvec_index n ~> o;

  to_vec o: o ~> vector 1 o;

  concat n o: vector n o ** o ~> vector (n+1) o;
}.

Coercion cava_arrow: Cava >-> Arrow.
Coercion cava_arrow_swap: Cava >-> ArrowSwap.
Coercion cava_arrow_drop: Cava >-> ArrowDrop.
Coercion cava_arrow_copy: Cava >-> ArrowCopy.
Coercion cava_arrow_loop: Cava >-> ArrowLoop.

Declare Scope cava_scope.
Bind Scope cava_scope with Cava.
Delimit Scope cava_scope with cava.

Open Scope cava_scope.

Definition cava_cat (_: Cava): Category := _.
Definition cava_obj (cava: Cava): Type := @object (@cava_cat cava).

Definition high {_: Cava}: unit ~> bit := constant true.
Definition low {_: Cava}: unit ~> bit := constant false.
