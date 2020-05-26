From Coq Require Import Bool List ZArith Setoid Classes.Morphisms FunctionalExtensionality.
Import ListNotations.

Require Import Cava.BitArithmetic.
Require Import Cava.Arrow.Arrow.

Require Import Cava.Netlist.

(******************************************************************************)
(* Evaluation as function evaluation, no delay elements or loops              *)
(******************************************************************************)

Section CoqEval.
  #[refine] Instance CoqCat : Category := {
    object := Type;
    morphism X Y := X -> Y;
    compose _ _ _ f g x := f (g x);
    id X x := x;

    morphism_equivalence x y f g := f = g;
  }.
  Proof.
    intros.
    unfold Proper.
    refine (fun f => _). intros.
    refine (fun g => _). intros.
    rewrite H.
    rewrite H0.
    auto.

    auto.
    auto.

    auto.
  Defined.

  Ltac simple_destruct :=
  match goal with
  | [H: ?X * ?Y |- _] => destruct H
  | [H: Datatypes.unit |- _] => destruct H
  end.
  Ltac simple_solve :=
    intros; simpl; extensionality xxx; repeat simple_destruct; auto.

  #[refine] Instance CoqArr : Arrow := {
    cat := CoqCat;
    unit := Datatypes.unit : Type ;
    product := prod;

    first _ _ _ f '(x, y) := (f x, y);
    second _ _ _ f '(x, y) := (x, f y);
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
  Proof.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.
    simple_solve.

    simple_solve; f_equal; inversion H; auto.
    simple_solve; f_equal; inversion H; auto.

    simple_solve.
    simple_solve.

    simple_solve.
    simple_solve.
  Defined.

  Instance Combinational : Cava := {
    bit := bool;
    bitvec n := bitVecTy bool n;

    constant b _ := b;
    constant_vec n v _ := v;

    not_gate '(b, tt) := negb b;
    and_gate '(x, (y, tt)) := andb x y;
    nand_gate '(x, (y, tt)) := negb (andb x y);
    or_gate '(x, (y, tt)) := orb x y;
    nor_gate '(x, (y, tt)) := negb (orb x y);
    xor_gate '(x, (y, tt)) := xorb x y;
    xnor_gate '(x, (y, tt)) := negb (xorb x y);
    buf_gate '(x, tt) := x;

    xorcy '(x, (y, tt)) := xorb x y;
    muxcy '(i,(t,(e,tt))) := if i then t else e;

    unsigned_add m n s '(av, (bv, tt)) :=
      let a := list_bits_to_nat av in
      let b := list_bits_to_nat bv in
      let c := (a + b)%N in
      nat_to_list_bits_sized s c;
  }.

  Example not_true: not_gate (true, tt) = false.
  Proof. reflexivity. Qed.
  Example not_false: not_gate (false, tt) = true.
  Proof. reflexivity. Qed.

End CoqEval.
