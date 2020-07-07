(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

From Coq Require Import Bool ZArith NaryFunctions Vector Lia.
From Arrow Require Import Category Arrow.
From Cava.Arrow Require Import CavaArrow PropArrow.

Import VectorNotations.
Import EqNotations.

Require Import Cava.BitArithmetic.

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

Fixpoint denote (ty: Kind): Type :=
  match ty with 
  | Tuple l r => denote l * denote r
  | Bit => bool
  | Vector ty n => Vector.t (denote ty) n
  | Unit => unit
  end.

Section instance.

Instance CoqKindMaybeCategory : Category Kind := {
  morphism X Y := denote X -> option (denote Y);
  compose _ _ _ f g := g >==> f;
  id X x := Some x;
}.

Instance CoqKindMaybeArrow : Arrow _ CoqKindMaybeCategory Unit Tuple := {
  first _ _ _ f i := match f (fst i) with | Some x => Some (x, snd i) | _ => None end;
  second _ _ _ f i := match f (snd i) with | Some y => Some (fst i, y) | _ => None end;

  cancelr X x := Some (fst x);
  cancell X x := Some (snd x);

  uncancell _ x := Some (tt, x);
  uncancelr _ x := Some (x, tt);

  assoc _ _ _ i := Some (fst (fst i), (snd (fst i), snd i));
  unassoc _ _ _ i := Some ((fst i, fst (snd i)), snd (snd i));
}.

Instance CombinationalDrop : ArrowDrop CoqKindMaybeArrow := { drop _ x := Some tt }.
Instance CombinationalCopy : ArrowCopy CoqKindMaybeArrow := { copy _ x := Some (pair x x) }.
Instance CombinationalSwap : ArrowSwap CoqKindMaybeArrow := { swap _ _ x := Some (snd x, fst x) }.
Instance CombinationalLoop : ArrowLoop CoqKindMaybeArrow := { loopl _ _ _ _ _ := None; loopr _ _ _ _ _ := None }.
Instance CombinationalSTKC : ArrowSTKC CoqKindMaybeArrow := { }.

#[refine] Instance Combinational : Cava := {
  cava_arrow := CoqKindMaybeArrow;
  constant b _ := Some b;
  constant_bitvec n v _ := Some (nat_to_bitvec_sized n (N.to_nat v));

  mk_module _ _ _name f := f;

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

  empty_vec o _ := Some (Vector.nil (denote o));
  index n o '(array, index) := 
    match Arith.Compare_dec.lt_dec (bitvec_to_nat index) n with
    | left Hlt => Some (nth_order array Hlt)
    | right Hnlt => None
    end;

  cons n o '(x, v) := Some (x :: v);
  snoc n o '(v, x) := 
    let v' := Some (v ++ [x]) 
    in match Nat.eq_dec (n + 1) (S n)  with 
      | left Heq => rew [fun x => option (denote (Vector o x))] Heq in v'
      | right Hneq => (ltac:(exfalso;lia))
      end;
  uncons n o v := Some (hd v, tl v);
  unsnoc n o v :=
    let v' := match Arith.Compare_dec.le_dec n (S n)  with 
      | left Hlt => take n Hlt v
      | right Hnlt => (ltac:(exfalso;lia))
      end in
    Some (v', last v);
  concat n m o '(x, y) := Some (Vector.append x y);

  split n m o H x :=
    match Nat.eq_dec n (m + (n - m)) with 
      | left Heq => Some (@Vector.splitat (denote o) m (n - m) (rew [Vector.t _]Heq in x))
      | right Hneq => (ltac:(exfalso;lia))
      end;

  slice n x y o H1 H2 v := 
    match Nat.eq_dec n (y + (n - y)) with 
      | left Heq =>
        let '(_, v) := splitat y (rew [fun x => Vector.t (denote o) x] Heq in v)
        in 
          match Nat.eq_dec (n-y) ((x - y + 1) + (n - x - 1)) with 
          | left Heq => _
          | right Hneq => (ltac:(exfalso;lia))
          end
      | right Hneq => (ltac:(exfalso;lia))
      end;
}.
Proof.
  (* slice *)
  - cbn.
    intros.
    rewrite Heq in v.
    apply (splitat (x-y+1)) in v.
    apply (fst) in v.
    exact (Some v).
Defined.

End instance.

Local Open Scope category_scope.

Definition wf_combinational {x y} (circuit: x ~[Combinational]~> y)
  := forall i, exists o, circuit i = Some o.

Lemma split_combinational {x y z}
  (circuit1: x ~[Combinational]~> y)
  (circuit2: y ~[Combinational]~> z)
  i
  : (circuit1 >>> circuit2 ) i
  = match circuit1 i with 
  | Some i' => circuit2 i'
  | None => None
  end.
Proof. auto. Qed.

Lemma wf_combinational_split {x y z}
  (circuit1: x ~[Combinational]~> y)
  (circuit2: y ~[Combinational]~> z)
  : wf_combinational circuit1 /\ wf_combinational circuit2
  -> wf_combinational (circuit1 >>> circuit2).
Proof.
  unfold wf_combinational in *; intros.
  - inversion H.
    specialize (H0 i).
    destruct H0.
    specialize (H1 x0).
    inversion H1.
    rewrite split_combinational.
    rewrite H0.
    eexists.
    rewrite H2.
    auto.
Qed.

Lemma second_is_combinational {x y z}:
  forall (circuit1: x ~[Combinational]~> y),
  wf_combinational circuit1 ->
  wf_combinational (second (z:=z) circuit1).
Proof.
  unfold wf_combinational.
  intros.
  cbn.
  specialize (H (snd i)).
  destruct (circuit1 (snd i)).
  eauto.
  inversion H.
  inversion H0.
Qed.

Lemma uncancelr_is_combinational {x}:
  wf_combinational (uncancelr (Arrow:=@cava_arrow Combinational) (x:=x)).
Proof.
  unfold wf_combinational.
  cbn.
  eauto.
Qed.

Lemma insert_rightmost_tt1_is_combinational: forall x,
  wf_combinational (insert_rightmost_tt1 x).
Proof.
  apply (well_founded_ind arg_length_order_wf _).
  intros.
  destruct x; [| cbn; unfold wf_combinational; eauto ..].
  unfold insert_rightmost_tt1.
  rewrite Fix_eq.
  destruct x2.
  * apply (second_is_combinational _).
    fold (@insert_rightmost_tt1 Combinational (Tuple x2_1 x2_2)).
    apply (H (Tuple x2_1 x2_2)).
    unfold arg_length_order; auto.
  * apply uncancelr_is_combinational.
  * apply (second_is_combinational _).
    fold (@insert_rightmost_tt1 Combinational Bit).
    apply (H Bit).
    unfold arg_length_order; auto.
  * apply (second_is_combinational _).
    fold (@insert_rightmost_tt1 Combinational (Vector x2 n)).
    apply (H (Vector x2 n)).
    unfold arg_length_order; auto.
  * intros.
    cbn.
    destruct x; auto.
    destruct x4; try rewrite (H0 _ _); auto.
Qed.

Lemma remove_right_unit_is_combinational {x y} (circuit: forall cava: Cava, x ~[cava]~> y)
  : wf_combinational (circuit Combinational) -> wf_combinational (insert_rightmost_tt1 _ >>> (circuit _)).
Proof.
  intros.
  apply (wf_combinational_split (insert_rightmost_tt1 x) (circuit _)).
  split.
  apply insert_rightmost_tt1_is_combinational.
  apply H.
Qed.

Lemma unsat_kind_false: forall y, (exists o : denote y, None = Some o) -> False.
Proof.
  intros.
  induction y; inversion H; inversion H0.
Qed.

Definition evaluate {x y}
  (circuit: forall cava: Cava, x ~> y)
  (wf: wf_combinational (circuit Combinational)) 
  (i: denote (remove_rightmost_unit x))
  : denote y.
Proof.
  apply remove_right_unit_is_combinational in wf.
  pose ((insert_rightmost_tt1 _ >>> circuit Combinational) i) as c'.
  specialize (wf i).
  set (v := (insert_rightmost_tt1 x >>> circuit Combinational) i) in *.
  destruct v.
  exact d.

  apply unsat_kind_false in wf.
  inversion wf.
Defined.

(* Ltac sub_prop :=
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
Defined. *)

Lemma not_gate_is_combinational: is_combinational (@not_gate).
Proof.
  unfold is_combinational.
  cbn.
  tauto.
Defined.

Lemma not_gate_wf: wf_combinational (not_gate).
Proof.
  cbv [wf_combinational not_gate Combinational].
  eauto.
Defined.

Ltac combinational_obvious :=
  cbv [wf_combinational];
  compute;
  eauto.

Example not_true: @not_gate Combinational true = Some false.
Proof. reflexivity. Qed.

Example not_true_with_wf: evaluate (@not_gate) not_gate_wf true = false.
Proof. compute. reflexivity. Qed.

Example not_false: @not_gate Combinational false = Some true.

Proof. reflexivity. Qed.