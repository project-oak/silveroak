From Coq Require Import Bool List ZArith Setoid Classes.Morphisms FunctionalExtensionality NaryFunctions VectorDef.
Import ListNotations.
Import VectorNotations.

Require Import Cava.BitArithmetic.
Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Instances.Constructive.

Require Import Cava.Netlist.
Require Import Cava.Types.

(******************************************************************************)
(* Evaluation as function evaluation, no delay elements or loops              *)
(******************************************************************************)

(* TODO: switch to coq ext lib's option monad*)
Notation "f >==> g" :=
  (fun x =>
  match f x with
  | Some y => g y
  | _ => None
  end)(at level 1).

Ltac simple_destruct :=
  match goal with
  | [H: ?X * ?Y |- _] => destruct H
  | [H: Datatypes.unit |- _] => destruct H
  end.

Ltac solve_optional :=
  cbv [fst snd];
  match goal with
  | [h1: ?x -> option _, h2: ?x |- _] => destruct (h1 h2); clear h1
  | [|- context[match ?X ?Y with | _ => _  end]] => destruct (X Y)
  end.

Ltac simple_solve :=
  intros; simpl; try let x := fresh in extensionality x; repeat simple_destruct; repeat solve_optional.

Hint Extern 3 => simple_solve : core.
Hint Extern 2 => solve_optional : core.

Lemma match_some: forall A B (x: option B) y (z: option A), (match x with | Some _ => z | None => None end = Some y) -> (z = Some y).
Proof.
  intros.
  destruct x.
  auto.
  inversion H.
Qed.

#[refine] Instance CoqCat : Category := {
  object := Type;
  morphism X Y := X -> option Y;
  compose _ _ _ f g := g >==> f;
  id X x := Some x;

  morphism_equivalence x y f g := f = g;
}.
Proof.
  intros.
  unfold Proper.
  refine (fun f => _). intros.
  refine (fun g => _). intros.
  rewrite H0.
  rewrite H.
  auto.
  auto.
  auto.
  auto.
Defined.

#[refine] Instance CoqArr : Arrow := {
  cat := CoqCat;
  unit := Datatypes.unit : Type ;
  product := prod;

  first _ _ _ f i := match f (fst i) with | Some x => Some (x, snd i) | _ => None end;
  second _ _ _ f i := match f (snd i) with | Some y => Some (fst i, y) | _ => None end;

  cancelr X x := Some (fst x);
  cancell X x := Some (snd x);

  uncancell _ x := Some (tt, x);
  uncancelr _ x := Some (x, tt);

  assoc _ _ _ i := Some (fst (fst i), (snd (fst i), snd i));
  unassoc _ _ _ i := Some ((fst i, fst (snd i)), snd (snd i));
}.
Proof.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
Defined.

Instance CombinationalDrop : ArrowDrop CoqArr := { drop _ x := Some tt }.
Instance CombinationalCopy : ArrowCopy CoqArr := { copy _ x := Some (pair x x) }.
Instance CombinationalSwap : ArrowSwap CoqArr := { swap _ _ x := Some (snd x, fst x) }.
Instance CombinationalLoop : ArrowLoop CoqArr := { loopl _ _ _ _ _ := None; loopr _ _ _ _ _ := None }.

(* Some of the equalities defined in CircuitLaws can't be solved with optional return,
they either need to be changed/removed or this evaluator needs a different representation
such as {H:Prop| H -> X -> Y } *)
(* #[refine] Instance CombinationalCircuitLaws : CircuitLaws CoqArr _ _ _ := {}. *)
(* Program Instance CombinationalCircuitLaws : CircuitLaws CoqArr _ _ _. *)

Fixpoint vec_to_nprod (A: Type) n (v: Vector.t A n): A^n :=
match v with
| [] => tt
| x::xs => (x, vec_to_nprod A _ xs)
end%vector.

#[refine] Instance Combinational : Cava := {
  cava_arrow := CoqArr;
  bit := bool;
  vector n o := Vector.t o n;

  constant b _ := Some b;
  constant_bitvec n v _ := Some (nat_to_bitvec_sized n (N.to_nat v));

  not_gate b := Some (negb b);
  and_gate '(x, y) := Some (andb x y);
  nand_gate '(x, y) := Some (negb (andb x y));
  or_gate '(x, y) := Some (orb x y);
  nor_gate '(x, y) := Some (negb (orb x y));
  xor_gate '(x, y) := Some (xorb x y);
  xnor_gate '(x, y) := Some (negb (xorb x y));
  buf_gate x := Some x;
  delay_gate _ _ := None;

  xorcy '(x, y) := Some (xorb x y);
  muxcy i := Some (if fst i then fst (snd i) else snd (snd i));

  unsigned_add m n s '(av, bv) :=
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a + b)%N in
    Some (Ndigits.N2Bv_sized s c);

  lut n f i :=
    let f' := NaryFunctions.nuncurry bool bool n f in
    Some (_);

  index_vec n o '(array, index) := _;
  to_vec o x := Some [x]%vector;
  append n o '(v, x) :=
    let z := (x :: v)%vector in
    Some _;

  concat n m o '(x, y) := Some (Vector.append x y);
  split n m o H x :=
    let y := @Vector.splitat o m (n - m) _ in
    Some y;
}.
Proof.
  - apply f'.
    simpl in i.
    apply vec_to_nprod.
    apply i.

  - cbv [cat CoqArr CoqCat morphism]; intros.
    apply bitvec_to_nat in index.
    destruct (lt_dec index n).
    apply (Some (nth_order array l)).

    (* bad index *)
    exact (None).

  - assert (n + 1 = S n).
    omega.
    rewrite H.
    auto.

  - assert ( m + (n - m) = n).
    omega.
    rewrite H0.
    auto.
Defined.

Definition wf_combinational {x y} (circuit: x ~> y) := forall i, {o | circuit i = Some o}.
Definition evaluate {x y} (circuit: x ~> y) (wf: wf_combinational circuit) (i: x): y.
Proof.
  cbv [morphism CoqCat wf_combinational] in *.
  specialize (wf i).
  inversion wf.
  apply x0.
Defined.

Lemma not_gate_wf: wf_combinational not_gate.
Proof.
  cbv [morphism CoqCat wf_combinational not_gate Combinational bit].
  intros.
  refine (exist _ _ _).
  f_equal.
Defined.

Ltac combinational_obvious :=
  cbv [wf_combinational];
  compute;
  eexists;
  f_equal.

(* Computing the terms is useful for e.g. extracting simple values *)
Ltac evaluate_to_terms circuit wf inputs :=
  let reduced := eval compute in
  (List.map (evaluate (toCava _ circuit) wf) inputs) in
  exact reduced.

Example not_true: not_gate true = Some false.
Proof. reflexivity. Qed.

Example not_true_with_wf: evaluate not_gate not_gate_wf true = false.
Proof. compute. reflexivity. Qed.

Example not_false: not_gate false = Some true.

Proof. reflexivity. Qed.
