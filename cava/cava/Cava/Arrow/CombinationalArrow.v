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

From Coq Require Import Bool ZArith NArith NaryFunctions Vector Lia.
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

Section instance.

Instance CoqKindMaybeCategory : Category Kind := {
  morphism X Y := denote_kind X -> option (denote_kind Y);
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
  constant_bitvec n v _ := Some (N2Bv_sized n v);

  mk_module _ _ _name f := f;

  not_gate b := Some (negb (fst b));
  and_gate '(x, y) := Some (andb x (fst y));
  nand_gate '(x, y) := Some (negb (andb x (fst y)));
  or_gate '(x, y) := Some (orb x (fst y));
  nor_gate '(x, y) := Some (negb (orb x (fst y)));
  xor_gate '(x, y) := Some (xorb x (fst y));
  xnor_gate '(x, y) := Some (negb (xorb x (fst y)));
  buf_gate x := Some (fst x);
  delay_gate _ _ := None;

  xorcy '(x, y) := Some (xorb x (fst y));
  muxcy i := Some (if fst i then fst (fst (snd i)) else snd (fst (snd i)));

  unsigned_add m n s '(av, (bv, _)) :=
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a + b)%N in
    Some (Ndigits.N2Bv_sized s c);

  unsigned_sub s '(av, (bv, _)) :=
    let a := Ndigits.Bv2N av in
    let b := Ndigits.Bv2N bv in
    let c := (a - b)%N in (*todo: This is likely incorrect on underflow *)
    Some (Ndigits.N2Bv_sized s c);

  lut n f '(i,_) :=
    let f' := NaryFunctions.nuncurry bool bool n f in
    Some (f' (vec_to_nprod _ _ i));

  empty_vec o _ := Some (Vector.nil (denote_kind o));
  index n o '(array, (index, _)) := 
    match Arith.Compare_dec.lt_dec (bitvec_to_nat index) n with
    | left Hlt => Some (nth_order array Hlt)
    | right Hnlt => None
    end;

  cons n o '(x, (v,_)) := Some (x :: v);
  snoc n o '(v, (x,_)) := 
    let v' := Some (v ++ [x]) 
    in match Nat.eq_dec (n + 1) (S n)  with 
      | left Heq => rew [fun x => option (denote_kind (Vector o x))] Heq in v'
      | right Hneq => (ltac:(exfalso;lia))
      end;
  uncons n o v := Some (hd (fst v), tl (fst v));
  unsnoc n o v :=
    let v' := match Arith.Compare_dec.le_dec n (S n)  with 
      | left Hlt => take n Hlt (fst v)
      | right Hnlt => (ltac:(exfalso; abstract lia))
      end in
    Some (v', last (fst v));
  concat n m o '(x, (y, _)) := Some (Vector.append x y);

  split n m o x :=
    Some (Vector.splitat n (fst x));

  slice n x y o H1 H2 v := 
    match Nat.eq_dec n (y + (n - y)) with 
      | left Heq =>
        let '(_, v) := splitat y (rew [fun x => Vector.t (denote_kind o) x] Heq in (fst v))
        in 
          match Nat.eq_dec (n-y) ((x - y + 1) + (n - x - 1)) with 
          | left Heq => _
          | right Hneq => (ltac:(exfalso; abstract lia))
          end
      | right Hneq => (ltac:(exfalso; abstract lia))
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

Lemma unsat_kind_false: forall y, (exists o : denote_kind y, None = Some o) -> False.
Proof.
  intros.
  induction y; inversion H; inversion H0.
Qed.

Definition combinational_evaluation {x y: Kind}
  (circuit: forall cava: Cava, x ~> y)
  (wf: wf_combinational (circuit Combinational)) 
  (i: denote_kind (remove_rightmost_unit x))
  : denote_kind y.
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

Lemma not_gate_wf: wf_combinational (not_gate).
Proof.
  cbv [wf_combinational not_gate Combinational].
  eauto.
Defined.

Ltac combinational_obvious :=
  cbv [wf_combinational];
  compute;
  eauto.

Example not_true: @not_gate Combinational (true, tt) = Some false.
Proof. reflexivity. Qed.

Example not_true_with_wf: combinational_evaluation (@not_gate) not_gate_wf true = false.
Proof. compute. reflexivity. Qed.

Example not_false: @not_gate Combinational (false, tt) = Some true.
Proof. reflexivity. Qed.