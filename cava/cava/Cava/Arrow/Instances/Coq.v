From Coq Require Import Program.Tactics.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Bool.Bvector.

Import ListNotations.

From Coq Require Import ZArith.

Require Import Cava.BitArithmetic.
Require Import Cava.Arrow.Arrow.

(* Arrow as function evaluation, no delay elements or loops *)
Section CoqEval.
  Instance CoqCat : Category := {
    object := Type;
    morphism X Y := X -> Y;
    compose _ _ _ f g x := f (g x);
    id X x := x;
  }.

  Instance CoqArr : Arrow := {
    unit := Datatypes.unit : Type;
    product := prod;

    fork _ _ _ f g x := (f x, g x);
    exl X Y := fst;
    exr X Y := snd;

    drop _ x := tt;
    copy _ x := pair x x;

    swap _ _ x := (snd x, fst x);

    uncancell _ x := (tt, x);
    uncancelr _ x := (x, tt);

    assoc _ _ _ '((x,y),z) := (x,(y,z));
    unassoc _ _ _ '(x,(y,z)) := ((x,y),z);
  }.

  Instance CoqCava : Cava := {
    bit := bool;
    bitvec n := Bvector n;

    constant b _ := b;
    constant_vec n v _ := v;

    not_gate b := negb b;
    and_gate '(x,y) := andb x y;
    nand_gate '(x,y) := negb (andb x y);
    or_gate '(x,y) := orb x y;
    nor_gate '(x,y) := negb (orb x y);
    xor_gate '(x,y) := xorb x y;
    xnor_gate '(x,y) := negb (xorb x y);
    buf_gate x := x;

    xorcy '(x,y) := xorb x y;
    muxcy '(x,y,z) := if x then y else z;

    unsigned_add m n s '(av, bv) :=
      let a := bitvec_to_nat av in
      let b := bitvec_to_nat bv in
      let c := a + b in
      nat_to_bitvec_sized s c;
  }.

  Example not_true: not_gate true = false.
  Proof. reflexivity. Qed.
  Example not_false: not_gate false = true.
  Proof. reflexivity. Qed.
End CoqEval.
