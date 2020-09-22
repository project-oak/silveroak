From Coq Require Import Setoid Classes.Morphisms.

Reserved Infix "~>" (at level 90, no associativity).
Reserved Infix "~[ C ]~>" (at level 90, no associativity).
Reserved Infix ">>>" (at level 53, right associativity).
Reserved Infix "=M=" (at level 54, no associativity).

Generalizable Variable object category.

(* more flexible than a haskell style category,
  which has morphisms between objects of type Hask.
  Here we have morphisms between objects of type object.
*)
Class Category (object: Type) := {
  category_object := object;
  morphism : object -> object -> Type
    where "a ~> b" := (morphism a b);

  id {x} : x ~> x;

  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "g >>> f" := (compose f g);
}.

Coercion category_object: Category >-> Sortclass.

Declare Scope category_scope.
Bind Scope category_scope with Category.
Delimit Scope category_scope with Category.

Notation "x ~> y" := (morphism x y) : category_scope.
Notation "x ~[ C ]~> y" := (@morphism _ C x y) (at level 90): category_scope.
Notation "g >>> f" := (compose f g) : category_scope.

Local Open Scope category_scope.

Class CategoryLaws `(category: Category) := {
  (* Setoid equivalence *)

  morphism_equivalence: forall x y (f g: x ~> y), Prop
    where "f =M= g" := (morphism_equivalence _ _ f g);
  morphism_setoid_equivalence : forall x y , Equivalence (morphism_equivalence x y);
  compose_respects_equivalence : forall x y z , Proper (morphism_equivalence y z ==> morphism_equivalence x y ==> morphism_equivalence x z) compose;

  id_left {x y} (f: x ~> y) : (id >>> f) =M= f;
  id_right {x y} (f: x ~> y) : (f >>> id) =M= f;

  associativity {x y z w} {f: x~>y} {g: y~>z} {h: z~>w} : (f >>> g) >>> h =M= f >>> (g >>> h);
}.

Bind Scope category_scope with CategoryLaws.
Delimit Scope category_scope with CategoryLaws.

Notation "f =M= g" := (morphism_equivalence _ _ f g) : category_scope.

Add Parametric Relation (object: Type) (C: Category object) (CL: CategoryLaws C) (x y: object): (morphism x y) (morphism_equivalence x y)
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (morphism_setoid_equivalence x y))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (morphism_setoid_equivalence x y))
  transitivity proved by (@Equivalence_Transitive _ _ (morphism_setoid_equivalence x y))
  as parametric_relation_eqv.

Hint Extern 1 => apply compose_respects_equivalence : category.
Hint Extern 1 => apply id_left : category.
Hint Extern 1 => apply id_right : category.

Add Parametric Morphism (object: Type) (C: Category object) (CL: CategoryLaws C) (x y z: object) : (@compose object C x y z)
  with signature (morphism_equivalence _ _ ==> morphism_equivalence _ _ ==> morphism_equivalence _ _)
  as parametric_morphism_comp.
Proof. auto with category. Defined.