From Coq Require Import Bool List ZArith Setoid Classes.Morphisms FunctionalExtensionality NaryFunctions.
Import ListNotations.

Require Import Cava.BitArithmetic.
Require Import Cava.Arrow.Arrow.

Require Import Cava.Netlist.
Require Import Cava.Types.

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

  Lemma replicate_object_is_nprod: forall n T, (replicate_object n T) = (nprod T n).
  Proof.
    intros.
    induction n; simpl; auto.
    f_equal.
    apply IHn.
  Qed.

  Lemma inc_nprod: forall n T, prod T (nprod T n) = (nprod T (S n)).
  Proof.
    intros.
    induction n; simpl; auto.
  Qed.

  #[refine] Instance Combinational : Cava := {
    representable t := match t with
      | Bit => bool
      | BitVec xs => denoteBitVecWith bool xs
      end;

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
    muxcy '(i,((t,e),tt)) := if i then t else e;

    unsigned_add m n s '(av, (bv, tt)) :=
      let a := list_bits_to_nat av in
      let b := list_bits_to_nat bv in
      let c := (a + b)%N in
      nat_to_list_bits_sized s c;

    lut n f i := 
      let f' := NaryFunctions.nuncurry bool bool n f in 
      _;

    index_array n xs '(array, (index, _)) := _; (* nth (N.to_nat (list_bits_to_nat index)) array 0; *)
    to_vec := _; (* nprod_to_list *)
  }.
  Proof.
    - apply f'.
      simpl in i.
      rewrite replicate_object_is_nprod in i.
      apply i.

    - intros.
      simpl; apply (list_bits_to_nat) in index; apply (N.to_nat) in index.
      destruct xs; simpl in *.
      * exact (nth index array false).
      * refine (nth index array _).

        (* bad index, return default value *)
        refine (match xs with
        | [] => _
        | _ :: _ => _
        end).
        exact ([  ]).
        exact ([  ]).

    - intros.
      destruct o
      ; rewrite replicate_object_is_nprod.
      * cbv [cat CoqArr CoqCat morphism].
        apply nprod_to_list.
      * cbv [cat CoqArr CoqCat morphism].
        destruct l.
        unfold denoteBitVecWith.
        apply nprod_to_list.
        cbv [cat CoqArr CoqCat morphism denoteBitVecWith].
        apply nprod_to_list.
  Defined.

  Example not_true: not_gate (true, tt) = false.
  Proof. reflexivity. Qed.
  Example not_false: not_gate (false, tt) = true.
  Proof. reflexivity. Qed.

End CoqEval.
