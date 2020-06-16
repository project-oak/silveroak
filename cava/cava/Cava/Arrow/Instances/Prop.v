From Coq Require Import Bool List ZArith Setoid Classes.Morphisms NaryFunctions VectorDef.
Import ListNotations.
Import VectorNotations.

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Instances.Constructive.

#[refine] Instance ConjPropKindCategory : Category Kind := {
  morphism X Y := Prop;
  compose _ _ _ f g := f /\ g;
  id X := True;

  morphism_equivalence x y f g := f <-> g;
}.
Proof.
  - split. intros. inversion H. auto. intros. split; auto.
  - split. intros. inversion H. auto. intros. split; auto.
  - split. 
    * intros. inversion H. inversion H1. auto.
    * intros. inversion H. inversion H0. auto.
Defined.

#[refine] Instance ConjPropKindArrow : Arrow _ ConjPropKindCategory Unit Tuple := {
  first _ _ _ p := p;
  second _ _ _ p := p;

  cancelr X := True;
  cancell X := True;

  uncancell _ := True;
  uncancelr _ := True;

  assoc _ _ _ := True;
  unassoc _ _ _ := True;
}.
Proof.
  - cbn. tauto.
  - cbn. tauto.
  - cbn. tauto.
  - cbn. tauto.
  - cbn. tauto.
  - cbn. tauto.
Defined.

Instance TrueDrop : ArrowDrop ConjPropKindArrow := { drop _ := True }.
Instance TrueCopy : ArrowCopy ConjPropKindArrow := { copy _ := True }.
Instance TrueSwap : ArrowSwap ConjPropKindArrow := { swap _ _ := True }.

Instance SubLoop : ArrowLoop ConjPropKindArrow := { loopl _ _ _ l := l; loopr _ _ _ l := l }.
Instance FalseLoop : ArrowLoop ConjPropKindArrow := { loopl _ _ _ _ := False; loopr _ _ _ _ := False }.

Instance NoDelays : Cava := {
  cava_arrow := ConjPropKindArrow;
  cava_arrow_loop := SubLoop;

  constant b := True;
  constant_bitvec n v := True;
  not_gate := True;
  and_gate := True;
  nand_gate := True;
  or_gate := True;
  nor_gate := True;
  xor_gate := True;
  xnor_gate := True;
  buf_gate := True;
  xorcy := True;
  muxcy := True;
  unsigned_add _ _ _ := True;
  lut _ _ := True;
  index_vec n o := True;
  slice_vec n x y o _ _ := True;
  to_vec o := True;
  append n o := True;
  concat n m o := True;
  split n m o H := True;

  delay_gate _ := False;
}.

Instance NoLoops : Cava := {
  cava_arrow := ConjPropKindArrow;
  cava_arrow_loop := FalseLoop;

  constant b := True;
  constant_bitvec n v := True;
  not_gate := True;
  and_gate := True;
  nand_gate := True;
  or_gate := True;
  nor_gate := True;
  xor_gate := True;
  xnor_gate := True;
  buf_gate := True;
  xorcy := True;
  muxcy := True;
  unsigned_add _ _ _ := True;
  lut _ _ := True;
  index_vec n o := True;
  slice_vec n x y o _ _ := True;
  to_vec o := True;
  append n o := True;
  concat n m o := True;
  split n m o H := True;
  delay_gate _ := True;
}.

(* Instance WfIndexing : Cava := {
  cava_arrow := ConjPropKindArrow;
  cava_arrow_loop := SubLoop;

  constant b := True;
  constant_bitvec n v := True;
  not_gate := True;
  and_gate := True;
  nand_gate := True;
  or_gate := True;
  nor_gate := True;
  xor_gate := True;
  xnor_gate := True;
  buf_gate := True;
  xorcy := True;
  muxcy := True;
  unsigned_add _ _ _ := True;
  lut _ _ := True;
  slice_vec n x y o _ _ := True;
  to_vec o := True;
  append n o := True;
  concat n m o := True;
  split n m o H := True;
  delay_gate _ := True;

  index_vec n o := forall x, x < Nat.log2_up n; (* this is not right; x needs to be related to the actual values it receives *)
}. *)

Definition is_combinational {i o: Kind} (c: forall (cava: Cava), i ~[cava]~> o) := 
  c NoLoops /\ c NoDelays.

Definition mkCombinational {i o: Kind} (c: forall (cava: Cava), i ~[cava]~> o)
  : c NoLoops -> c NoDelays -> is_combinational c.
Proof.
  intros.
  unfold is_combinational.
  tauto.
Qed.

Lemma is_combinational_first: forall x y z circuit,
  is_combinational (toCava (@First x y z circuit)) =   
  is_combinational (toCava circuit).
Proof.
  intros.
  tauto.
Qed.

Lemma is_combinational_second: forall x y z circuit,
  is_combinational (toCava (@Second x y z circuit)) =   
  is_combinational (toCava circuit).
Proof.
  intros.
  tauto.
Qed.

Lemma modular_prop: forall (x y z : Kind)
  (A: Arrow Kind ConjPropKindCategory Unit Tuple)
  (f: x ~[A]~> y) (g: y ~[A]~> z),
  (f >>> g) = 
  (g /\ f).
Proof.
  intros.
  tauto.
Qed.

Lemma decompose_combinational (x y z : Kind) (f: structure x y) (g: structure y z):
  is_combinational (toCava (Compose g f)) -> 
  is_combinational (toCava g) /\ is_combinational (toCava f).
Proof.
  intros.
  unfold is_combinational in *.
  cbn in H.
  tauto.
Qed.

Section example.
  Definition ex_loopr {x y z: Kind} (cava: Cava) (c: x**z ~[cava]~> y**z): x ~[cava]~> y
    := loopr c.
  Definition ex_loopl {x y z: Kind} (cava: Cava) (c: z**x ~[cava]~> z**y): x ~[cava]~> y
    := loopl c.

  Lemma loopl_is_not_combinational : forall (x y z: Kind) (c: forall (cava: Cava), z**x ~[cava]~> z**y),
    ~ is_combinational (fun cava => ex_loopl cava (c cava)).
  Proof.
    intros.
    unfold is_combinational.
    tauto.
  Qed.

  Lemma loopr_is_not_combinational : forall (x y z: Kind) (c: forall (cava: Cava), x**z ~[cava]~> y**z),
    ~ is_combinational (fun cava => ex_loopr cava (c cava)).
  Proof.
    intros.
    unfold is_combinational.
    tauto.
  Qed.
End example.