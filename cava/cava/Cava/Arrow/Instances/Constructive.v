From Coq Require Import Bool.Bool.
From Coq Require Import Bool.Bvector.

Require Import Cava.BitArithmetic.
Require Import Cava.Arrow.Arrow.

Set Implicit Arguments.

Inductive type :=
| Bit:    type
| BitVec: nat -> type.

Inductive tree : Type :=
| Empty : tree
| Leaf : type -> tree
| Branch : tree -> tree -> tree. 

Inductive structure: tree -> tree -> Type :=
| Id:          forall x, structure x x
| Compose:     forall x y z, structure y z -> structure x y -> structure x z
| Copy:        forall x, structure x (Branch x x)
| Drop:        forall x, structure x Empty
| Swap:        forall x y, structure (Branch x y) (Branch y x)

| First:       forall x y z, structure x y -> structure (Branch x z) (Branch y z)
| Second:      forall x y z, structure x y -> structure (Branch z x) (Branch z y)

| Exl:         forall x y, structure (Branch x y) x
| Exr:         forall x y, structure (Branch x y) y

| Uncancell:   forall x, structure x (Branch Empty x)
| Uncancelr:   forall x, structure x (Branch x Empty)

| Assoc:       forall x y z, structure (Branch (Branch x y) z) (Branch x (Branch y z))
| Unassoc:     forall x y z, structure (Branch x (Branch y z)) (Branch (Branch x y) z)

| Constant:    bool -> structure Empty (Leaf Bit)
| ConstantVec: forall n, Bvector n -> structure Empty ((Leaf (BitVec n)))

| NotGate:     structure (Branch (Leaf Bit) Empty) (Leaf Bit)
| AndGate:     structure (Branch (Leaf Bit) (Branch (Leaf Bit) Empty)) (Leaf Bit)
| NandGate:    structure (Branch (Leaf Bit) (Branch (Leaf Bit) Empty)) (Leaf Bit)
| OrGate:      structure (Branch (Leaf Bit) (Branch (Leaf Bit) Empty)) (Leaf Bit)
| NorGate:     structure (Branch (Leaf Bit) (Branch (Leaf Bit) Empty)) (Leaf Bit)
| XorGate:     structure (Branch (Leaf Bit) (Branch (Leaf Bit) Empty)) (Leaf Bit)
| XnorGate:    structure (Branch (Leaf Bit) (Branch (Leaf Bit) Empty)) (Leaf Bit)
| BufGate:     structure (Branch (Leaf Bit) Empty) (Leaf Bit)

| Xorcy:       structure (Branch (Leaf Bit) (Branch (Leaf Bit) Empty)) (Leaf Bit)
| Muxcy:       structure (Branch (Leaf Bit) (Branch (Leaf Bit) (Branch (Leaf Bit) Empty))) (Leaf Bit)

| UnsignedAdd: forall a b s, structure (Branch ((Leaf (BitVec a))) (Branch ((Leaf (BitVec b))) Empty)) ((Leaf (BitVec s))).

Arguments Id [x].
Arguments Compose [x y z].

Inductive st_equiv : forall (i o: tree), structure i o -> structure i o -> Prop :=
| st_refl:    forall x y f, @st_equiv x y f f
| st_sym:     forall x y f g, st_equiv g f -> @st_equiv x y f g
| st_trans:   forall x y f g h, st_equiv f g -> st_equiv g h -> @st_equiv x y f h
| st_compose: forall x y z f g h i, @st_equiv x y f g -> @st_equiv y z h i -> st_equiv (Compose h f) (Compose i g)
| st_id_left: forall x y f, @st_equiv x y (Compose f Id) f
| st_id_right:forall x y f, @st_equiv x y (Compose Id f) f
| st_assoc:   forall x y z w
                    (f: structure x y) (g: structure y z) (h: structure z w),
                    @st_equiv x w (Compose h (Compose g f)) (Compose (Compose h g) f)

| st_exl_unit_uncancelr: forall x, st_equiv (Compose (Uncancelr x) (Exl x Empty)) Id
| st_exr_unit_uncancell: forall x, st_equiv (Compose (Uncancell x) (Exr Empty x)) Id

| st_uncancelr_exl: forall x, st_equiv (Compose (Exl x Empty) (Uncancelr x)) Id
| st_uncancell_exr: forall x, st_equiv (Compose (Exr Empty x) (Uncancell x)) Id

| st_drop_annhilates: forall x y (f: structure x y), st_equiv (Compose (Drop y) f) (Drop x)

| st_exl_unit_is_drop: forall x, st_equiv (Exl Empty x) (Drop _)
| st_exr_unit_is_drop: forall x, st_equiv (Exr x Empty) (Drop _)

| st_first_first:   forall x y z w (f: structure x y) (g: structure y z), st_equiv (Compose (First w g) (First _ f)) (First _ (Compose g f))
| st_second_second: forall x y z w (f: structure x y) (g: structure y z), st_equiv (Compose (Second w g) (Second _ f)) (Second _ (Compose g f))

| st_swap_swap: forall x y, st_equiv (Compose (Swap _ _) (Swap x y)) Id

| st_first_id: forall x w, st_equiv (@First x x w Id) Id
| st_second_id: forall x w, st_equiv (@Second x x w Id) Id

| st_first_f: forall x y w (f: structure x y) (g: structure x y), st_equiv f g -> st_equiv (First w f) (First w g)
| st_second_f: forall x y w (f: structure x y) (g: structure x y), st_equiv f g -> st_equiv (Second w f) (Second w g)

| st_assoc_unassoc: forall x y z, st_equiv (Compose (Unassoc x y z) (Assoc x y z)) Id
| st_unassoc_assoc: forall x y z, st_equiv (Compose (Assoc x y z) (Unassoc x y z)) Id

| st_first_exl: forall x y w f, st_equiv (Compose (Exl _ _) (@First x y w f)) (Compose f (Exl _ _))
| st_second_exr: forall x y w f, st_equiv (Compose (Exr _ _) (@Second x y w f)) (Compose f (Exr _ _)) 
.

Fixpoint structural_simplification {i o} (s: structure i o): structure i o.
Proof.
  destruct s eqn:E; try constructor.
  destruct s0_1 eqn:E1;
  try exact (Drop _);
  try exact s0_2;
  apply s.
  apply s0.
  apply s0.
  apply b.
  apply b.
Defined.

Hint Immediate st_refl : core.
Hint Immediate st_sym : core.
Hint Immediate st_trans : core.

Definition denoteType `{Cava} (t: type)
  : object :=
match t with
| Bit       => bit
| BitVec n  => bitvec n
end.

Fixpoint denoteTree `{Cava} (t: tree)
  : object :=
match t with
| Empty => unit
| Leaf l => denoteType l
| Branch x y => denoteTree x ** denoteTree y
end.

Fixpoint toCava {i o} (Cava:Cava) (expr: structure i o)
  : (denoteTree i) ~> (denoteTree o) :=
match expr with
| Id                => id
| Compose g f       => compose (toCava Cava g) (toCava Cava f)
| Copy x            => copy
| Drop x            => drop
| Swap x y          => swap

| First _ f     => first (toCava Cava f)
| Second _ f    => second (toCava Cava f)

| Exl _ _           => exl
| Exr _ _           => exr

| Uncancell _       => uncancell
| Uncancelr _       => uncancelr

| Assoc _ _ _       => assoc
| Unassoc _ _ _     => unassoc

| Constant b        => constant b
| @ConstantVec n v   => constant_vec n v

| NotGate           => not_gate
| AndGate           => and_gate
| NandGate          => nand_gate
| OrGate            => or_gate
| NorGate           => nor_gate
| XorGate           => xor_gate
| XnorGate          => xnor_gate
| BufGate           => buf_gate

| Xorcy             => xorcy
| Muxcy             => muxcy

| UnsignedAdd a b s => unsigned_add a b s
end.

#[refine] Instance ConstructiveCat : Category := {
  object := tree;
  morphism X Y := structure X Y;
  compose X Y Z f g := Compose f g;
  id X := Id;

  morphism_equivalence x y f g := st_equiv f g;
}.
Proof.
  intros.
  apply RelationClasses.Build_Equivalence.
  unfold RelationClasses.Reflexive. auto. 
  unfold RelationClasses.Symmetric. auto.
  unfold RelationClasses.Transitive. intros. apply (st_trans H H0).

  intros.
  unfold Morphisms.Proper.
  refine (fun f => _). intros.
  refine (fun g => _). intros.
  apply (st_compose H0 H).

  intros. exact (st_id_left f).
  intros. exact (st_id_right f).
  intros. exact (st_assoc f g h).
Defined.

Instance ConstructiveArr : Arrow := {
  cat := ConstructiveCat;
  unit := Empty;
  product := Branch;

  first _ _ _ f := First _ f;
  second _ _ _ f := Second _ f;
  exl X Y := Exl X Y;
  exr X Y := Exr X Y;

  drop X := Drop X;
  copy X := Copy X;

  swap X Y := Swap X Y;

  uncancell X := Uncancell X;
  uncancelr X := Uncancelr X;

  assoc X Y Z := Assoc X Y Z;
  unassoc X Y Z := Unassoc X Y Z;


  exl_unit_uncancelr := st_exl_unit_uncancelr;
  exr_unit_uncancell := st_exr_unit_uncancell;

  uncancelr_exl := st_uncancelr_exl;
  uncancell_exr := st_uncancell_exr;

  drop_annhilates := st_drop_annhilates;

  exl_unit_is_drop := st_exl_unit_is_drop;
  exr_unit_is_drop := st_exr_unit_is_drop;

  first_first := st_first_first;
  second_second := st_second_second;

  swap_swap := st_swap_swap;

  first_id := st_first_id;
  second_id := st_second_id;

  first_f := st_first_f;
  second_f := st_second_f;

  assoc_unassoc := st_assoc_unassoc;
  unassoc_assoc := st_unassoc_assoc;

  first_exl := st_first_exl;
  second_exr := st_second_exr;
}.

Instance ConstructiveCava : Cava := {
  bit := Leaf Bit;
  bitvec n := (Leaf (BitVec n));

  constant b := Constant b;
  constant_vec n v := ConstantVec v;

  not_gate := NotGate;
  and_gate := AndGate;
  nand_gate := NandGate;
  or_gate := OrGate;
  nor_gate := NorGate;
  xor_gate := XorGate;
  xnor_gate := XnorGate;
  buf_gate := BufGate;

  xorcy := Xorcy;
  muxcy := Muxcy;

  unsigned_add m n s := UnsignedAdd m n s;
}.
