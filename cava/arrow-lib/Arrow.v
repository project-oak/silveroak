From Arrow Require Import Category.

Local Open Scope category_scope.

Reserved Infix "**" (at level 30, right associativity).

Generalizable Variable unit product.

Class DecidableEquality T := {
  eq_dec: forall x y : T, {x = y} + {x <> y}
}.

(* generalized arrow *)
Class Arrow (object: Type) (category: Category object) (unit: object) (product: object -> object -> object) := {
  arrow_category := category;
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
}.

Coercion arrow_category: Arrow >-> Category.

Declare Scope arrow_scope.
Bind Scope arrow_scope with Arrow.
Delimit Scope arrow_scope with Arrow.

Notation "x ** y" := (product x y)
  (at level 30, right associativity) : arrow_scope.

Class ArrowLaws 
  (object: Set) 
  (category: Category object) (category_laws: CategoryLaws category) 
  (unit: object) (product: object -> object -> object) (A: Arrow object category unit product)
  := {
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

Local Open Scope arrow_scope.

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

Class ArrowConstant
  object (category: Category object) 
  unit prod (A: Arrow object category unit prod) 
  (r: object) t
  := {
  constant : t -> (unit ~> r);
}.

Inductive void := .

Lemma void_is_false: void -> False.
Proof.
  intros.
  destruct H.
Qed.

Class ArrowSum
  object (category: Category object) 
  void either (ASum: Arrow object category void either) 
  := {
  merge {x} : (either x x) ~> x;
  never {x} : void ~> x;
}.

(*
Class ArrowApply := {
  app {x y}: (x~>y)**y ~> x:
}. 

Class ArrowProd := {
  prod_copy {x} : x ~> (x<*>x):
  prod_drop {x} : x ~> v;
}. 
*)

Class ArrowSTKC 
  `(A: Arrow) 
  := {
  stkc_arrow := A;
  stkc_arrow_drop :> ArrowDrop A;
  stkc_arrow_swap :> ArrowSwap A;
  stkc_arrow_copy :> ArrowCopy A;
}.

Coercion stkc_arrow: ArrowSTKC >-> Arrow.
Coercion stkc_arrow_drop: ArrowSTKC >-> ArrowDrop.
Coercion stkc_arrow_swap: ArrowSTKC >-> ArrowSwap.
Coercion stkc_arrow_copy: ArrowSTKC >-> ArrowCopy.

Section arrowstkc.
  Context {object: Type}.
  Context {unit: object}.
  Context {product: object -> object -> object}.

  Inductive ArrowStructure := 
    | Id: object -> ArrowStructure
    | Assoc: object -> object -> object -> ArrowStructure
    | Unassoc: object -> object -> object -> ArrowStructure
    | Cancelr: object -> ArrowStructure
    | Cancell: object -> ArrowStructure
    | Uncancell: object -> ArrowStructure
    | Uncancelr: object -> ArrowStructure
    | Copy: object -> ArrowStructure
    | Drop: object -> ArrowStructure
    | Swap: object -> object -> ArrowStructure.

  Inductive ArrowComposition :=
    | Compose: object -> object -> object -> ArrowComposition
    | First: object -> object -> object -> ArrowComposition
    | Second: object -> object -> object -> ArrowComposition.

  Fixpoint arrow_input (a: ArrowStructure): object :=
    match a with
    | Id x => x
    | Assoc x y z => (product (product x y) z)
    | Unassoc x y z => (product x (product y z))
    | Cancelr x => product x unit
    | Cancell x => product unit x
    | Uncancell x => x
    | Uncancelr x => x 
    | Copy x => x
    | Drop x => x
    | Swap x y => product x y
    end.

  Fixpoint arrow_output (a: ArrowStructure): object :=
    match a with
    | Id x => x
    | Assoc x y z => (product x (product y z))
    | Unassoc x y z => (product (product x y) z)
    | Cancelr x => x
    | Cancell x => x
    | Uncancell x => product unit x
    | Uncancelr x => product x unit 
    | Copy x => product x x
    | Drop x => unit
    | Swap x y => product y x
    end.
End arrowstkc.