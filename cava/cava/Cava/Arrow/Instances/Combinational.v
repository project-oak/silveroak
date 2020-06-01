From Coq Require Import Bool List ZArith Setoid Classes.Morphisms FunctionalExtensionality NaryFunctions VectorDef.
Import ListNotations.
Import VectorNotations.

Require Import Cava.BitArithmetic.
Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Instances.Constructive.
Require Import Cava.Arrow.Instances.Prop.

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

Ltac solve_optional :=
  cbv [fst snd];
  match goal with
  | [h1: ?x -> option _, h2: ?x |- _] => destruct (h1 h2); clear h1
  | [|- context[match ?X ?Y with | _ => _  end]] => destruct (X Y)
  end.

Ltac simple_solve :=
  intros; simpl;
  try let x := fresh in extensionality x;
  repeat solve_optional; auto.

Fixpoint denote (ty: Kind): Type :=
  match ty with 
  | Tuple l r => denote l * denote r
  | Bit => bool
  | Vector n ty => Vector.t (denote ty) n
  | Unit => unit
  end.

#[refine] Instance CoqKindMaybeCategory : Category Kind := {
  morphism X Y := denote X -> option (denote Y);
  compose _ _ _ f g := g >==> f;
  id X x := Some x;

  morphism_equivalence x y f g := f = g;
}.
Proof.
  - intros.
    unfold Proper.
    refine (fun f => _). intros.
    refine (fun g => _). intros.
    rewrite H0.
    rewrite H.
    auto.
  - auto.
  - simple_solve.
  - simple_solve.
Defined.

#[refine] Instance CoqKindMaybeArrow : Arrow _ CoqKindMaybeCategory Unit Tuple := {
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
  - simple_solve.
  - simple_solve.
  - simple_solve.
  - simple_solve.
  - simple_solve.
  - simple_solve.
Defined.

Instance CombinationalDrop : ArrowDrop CoqKindMaybeArrow := { drop _ x := Some tt }.
Instance CombinationalCopy : ArrowCopy CoqKindMaybeArrow := { copy _ x := Some (pair x x) }.
Instance CombinationalSwap : ArrowSwap CoqKindMaybeArrow := { swap _ _ x := Some (snd x, fst x) }.
Instance CombinationalLoop : ArrowLoop CoqKindMaybeArrow := { loopl _ _ _ _ _ := None; loopr _ _ _ _ _ := None }.

#[refine] Instance Combinational : Cava := {
  cava_arrow := CoqKindMaybeArrow;
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
    Some (f' (vec_to_nprod _ _ i));

  index_vec n o '(array, index) := _;
  slice_vec n x y o H v := _;
  to_vec o x := Some [x]%vector;
  append n o '(v, x) :=
    let z := (x :: v)%vector in
    Some _;

  concat n m o '(x, y) := Some (Vector.append x y);
  split n m o H x :=
    let y := @Vector.splitat (denote o) m (n - m) _ in
    Some y;
}.
Proof.
  (* index_vec *)
  - apply bitvec_to_nat in index.
    destruct (lt_dec index n).
    apply (Some (nth_order array l)).

    (* bad index *)
    exact (None).

  (* slice_vec *)
  - cbn.
    intros.
    assert (n = y + (n - y)).
    omega.
    rewrite H0 in X.
    apply (splitat y) in X.
    apply (snd) in X.
    assert (n - y = (x - y + 1) + (n - x - 1)).
    omega.
    rewrite H1 in X.
    apply (splitat (x-y+1)) in X.
    apply (fst) in X.
    exact (Some X).

  (* append *)
  - assert (n + 1 = S n).
    omega.
    rewrite H.
    auto.

  (* split *)
  - assert ( m + (n - m) = n).
    omega.
    rewrite H0.
    auto.
Defined.

Definition wf_combinational {x y} (circuit: x ~> y) := forall i, {o | circuit i = Some o}.

Definition evaluate {x y} (circuit: x ~> y) (wf: wf_combinational circuit) (i: denote x): denote y.
Proof.
  specialize (wf i).
  inversion wf.
  apply x0.
Defined.

Ltac sub_prop :=
    match goal with
    | [H: is_combinational (toCava ?X) |- _] => 
      unfold is_combinational in H; cbn in H; inversion H; clear H
    end;
    repeat match goal with
    | [ H: ?circuit NoLoops /\ _ |- _] => destruct H
    | [ H: ?circuit NoDelays /\ _ |- _] => destruct H
    end;
    repeat match goal with
    | [ H1: ?circuit NoLoops 
      , H2: ?circuit NoDelays
      |- _] => apply (mkCombinational circuit H1) in H2; clear H1
    end.

Ltac destruct_tuples :=
  match goal with
  | [H: denote (Tuple _ _) |- _] => destruct H; cbn
  end. 

Lemma combinational_circuit_has_value {i o}
  (circuit: structure i o)
  (wf_indexing: forall n o x, {y | toCava (@IndexVec n o) Combinational x = Some y})
  (combinational: is_combinational (toCava circuit))
  : forall x, {y | toCava circuit Combinational x = Some y}.
Proof.
  Hint Extern 3 => 
    repeat match goal with
    | [H: False |- _] => inversion H
    | [H: None = Some _ |- _] => inversion H
    | [H: exists _, None = Some _ |- _] => inversion H
    | [H: Some _ = Some _ |- _] => f_equal
    end : core. 
  Hint Extern 50 =>
    match goal with
    | [ H: ?X
      , H1: is_combinational (toCava ?circuit) 
      , H2: is_combinational (toCava ?circuit) -> forall (x:?X), _ |- _ ] => apply H2 with (x:=H) in H1
    end : core.

  Hint Extern 51 =>
    match goal with
    | [ H: sig (fun y => toCava _ Combinational ?X = Some y) |- _] => destruct H
    end : core.
  Hint Extern 99 => 
    match goal with
    | [|- context[toCava ?circuit Combinational ?x] ] => destruct (toCava circuit Combinational x)
    end : core.

  intros.
  induction circuit; cbn; try destruct_tuples; try sub_prop; eauto.

  cbn in wf_indexing.

  - specialize (wf_indexing n o (d,d0)).
    cbn in wf_indexing.
    apply wf_indexing.
Qed.

Definition evaluate2 {i o}
  (circuit: structure i o)
  (wf_indexing: forall n o x, {y | toCava (@IndexVec n o) Combinational x = Some y})
  (combinational: is_combinational (toCava circuit))
  : denote i -> denote o.
Proof.
  refine (fun x => let f := toCava circuit Combinational x in _).
  pose (combinational_circuit_has_value circuit wf_indexing combinational x).
  inversion s.
  apply x0.
Defined.

Lemma not_gate_is_combinational: is_combinational (@not_gate).
Proof.
  unfold is_combinational.
  cbn.
  tauto.
Defined.

Lemma not_gate_wf: wf_combinational (not_gate).
Proof.
  cbv [wf_combinational not_gate Combinational].
  intros.
  refine (exist _ _ _).
  auto.
Defined.

Ltac combinational_obvious :=
  cbv [wf_combinational];
  compute;
  eexists;
  f_equal.

(* Computing the terms is useful for e.g. extracting simple values *)
Ltac evaluate_to_terms circuit wf inputs :=
  let reduced := eval compute in
  (List.map (evaluate (toCava circuit _) wf) inputs) in
  exact reduced.

Example not_true: not_gate true = Some false.
Proof. reflexivity. Qed.

Example not_true_with_wf: evaluate not_gate not_gate_wf true = false.
Proof. compute. reflexivity. Qed.

Example not_false: not_gate false = Some true.

Proof. reflexivity. Qed.