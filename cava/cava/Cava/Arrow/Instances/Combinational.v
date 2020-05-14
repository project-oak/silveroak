From Coq Require Import Bool.Bool.
From Coq Require Import Bool.Bvector.

Require Import Cava.BitArithmetic.
Require Import Cava.Arrow.Arrow.

From Coq Require Import Setoid.
From Coq Require Import Classes.Morphisms.

Require Import FunctionalExtensionality.

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
    intros; simpl; extensionality z; repeat simple_destruct; auto.

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

    intros.
    refine (exist_pair (prod x Datatypes.unit~>x) (x~> prod x Datatypes.unit) _ fst (fun x => pair x tt)  _).
    simpl.
    split.
    simple_solve.
    auto.

    intros.
    inversion X.
    inversion H.
    inversion H0.
    inversion H1.
    refine (exist_pair (prod a x ~> prod a y) (prod a y ~> prod a x) _
      (fun '(a,b) => (a, x0 b))
      (fun '(a,b) => (a, y0 b))
      _).
    
    simpl.
    split.

    - extensionality z.
      destruct z.
      f_equal.
      apply (f_equal (fun f => f x1)) in H3.
      auto.

    - extensionality z.
      destruct z.
      f_equal.
      apply (f_equal (fun f => f y1)) in H4.
      auto.
  Defined.

  Instance Combinational : Cava := {
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
    muxcy '(i,(t,e)) := if i then t else e;

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