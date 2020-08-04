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
From Arrow Require Import Category Arrow Kappa.
From Cava.Arrow Require Import CavaArrow PropArrow.

Import VectorNotations.
Import EqNotations.

Require Import Cava.BitArithmetic.

Section instance.

(* Coq will infer the evaluated type of 'denote_kind ty', rather than 'denote_kind ty'
when giving constant values (e.g. 'tt'), so we define notation to apply the 
correct type annotation *)
Notation fun_s ty f := (existT _ _ (f : _ -> denote_kind ty -> (_ * denote_kind ty))).

Definition evalMorphism X Y := { state: Kind & denote_kind X -> denote_kind state -> (denote_kind Y * denote_kind state) }.
Definition evalProjState {X Y} (m: evalMorphism X Y): Kind := projT1 m. 

Instance EvalCategory : Category Kind := {
  morphism := evalMorphism;
  compose _ _ _ f g := 
    fun_s (Tuple (evalProjState g) (evalProjState f)) (
      fun x lr =>
      let '(l,r) := lr in
      let (x, l) := (projT2 g) x l in
      let (x, r) := (projT2 f) x r in
      (x, (l, r))
    );
  id X := fun_s Unit (fun x _ => (x, tt : denote_kind Unit));
}.

Instance EvalArrow : Arrow _ EvalCategory Unit Tuple := {
  first _ _ _ f := fun_s (evalProjState f) (fun i s =>
    let (x, s) := (projT2 f) (fst i) s in
    ((x, snd i), s : denote_kind (evalProjState f))
  );
  second _ _ _ f := fun_s (evalProjState f) (fun i s =>
    let (x, s) := (projT2 f) (snd i) s in
    ((fst i, x), s)
  );

  cancelr X := fun_s Unit (fun i s => (fst i, tt));
  cancell X := fun_s Unit (fun i s => (snd i, tt));

  uncancell X := fun_s Unit (fun i s => ((tt, i), tt));
  uncancelr X := fun_s Unit (fun i s => ((i, tt), tt));

  assoc _ _ _ := fun_s Unit (fun i s => ((fst (fst i), (snd (fst i), snd i)), tt));
  unassoc _ _ _ := fun_s Unit (fun i s => (((fst i, fst (snd i)), snd (snd i)), tt));
}.

Instance EvalDrop : ArrowDrop EvalArrow := { drop _ := fun_s Unit (fun i s => (tt, tt)) }.
Instance EvalCopy : ArrowCopy EvalArrow := { copy _ := fun_s Unit (fun i s => ((pair i i), tt)) }.
Instance EvalSwap : ArrowSwap EvalArrow
  := { swap _ _ := fun_s Unit (fun i s => ((snd i, fst i), tt)) }.
Instance EvalLoop : ArrowLoop EvalArrow := {
  loopl _ _ Z f := 
    fun_s (Tuple Z (evalProjState f)) (fun i s => 
      let '((oz, o), s) := (projT2 f) (fst s, i) (snd s) in
      (o, (oz, s))
    );
  loopr _ _ Z f := 
    fun_s (Tuple (evalProjState f) Z) (fun i s => 
      let '((o, oz), s) := (projT2 f) (i, snd s) (fst s) in
      (o, (s, oz))
    );
}.
Instance EvalSTKC : ArrowSTKC EvalArrow := { }.

#[refine] Instance EvalCava : Cava := {
  cava_arrow := EvalArrow;
  constant b := fun_s Unit (fun _ _ => (b, tt));
  constant_bitvec n v := fun_s Unit (fun _ _ => (N2Bv_sized n v, tt));

  mk_module _ _ _name f := f;

  not_gate := fun_s Unit (fun i _ => (negb (fst i), tt));
  and_gate := fun_s Unit (fun '(x, (y, _)) _ => (andb x y, tt));
  nand_gate := fun_s Unit (fun '(x, (y, _)) _ => (negb (andb x y), tt));
  or_gate := fun_s Unit (fun '(x, (y, _)) _ => (orb x y, tt));
  nor_gate := fun_s Unit (fun '(x, (y, _)) _ => (negb (orb x y), tt));
  xor_gate := fun_s Unit (fun '(x, (y, _)) _ => (xorb x y, tt));
  xnor_gate := fun_s Unit (fun '(x, (y, _)) _ => (negb (xorb x y), tt));

  buf_gate := fun_s Unit (fun i _ => (fst i, tt));
  delay_gate X := fun_s X (fun i s => (s, fst i));

  xorcy := fun_s Unit (fun '(x, (y, _)) _ => (xorb x y, tt));
  muxcy := fun_s Unit (fun (i: (bool*((bool*bool)*unit))) _ => (if fst i then fst (fst (snd i)) else snd (fst (snd i)), tt));

  unsigned_add m n s := fun_s Unit (fun '(x, (y,_)) _ => 
    let a := Ndigits.Bv2N x in
    let b := Ndigits.Bv2N y in
    let c := (a + b)%N in
    (Ndigits.N2Bv_sized s c, tt)
  );

  unsigned_sub s := fun_s Unit (fun '(x, (y, _)) _ => 
    let a := Ndigits.Bv2N x in
    let b := Ndigits.Bv2N y in
    let c := (a - b)%N in(*todo: This is likely incorrect on underflow *)
    (Ndigits.N2Bv_sized s c, tt)
  );

  lut n f := fun_s Unit (fun i _ => 
    let f' := NaryFunctions.nuncurry bool bool n f in
    (f' (vec_to_nprod _ _ (fst i)), tt)
  );

  empty_vec o := fun_s Unit (fun i _ => (Vector.nil (denote_kind o),tt));
  index n o := fun_s Unit (fun '(array, (index,_)) _ => 
    match Arith.Compare_dec.lt_dec (bitvec_to_nat index) n with
    | left Hlt => (nth_order array Hlt, tt)
    | right Hnlt => (kind_default _, tt)
    end);

  cons n o := fun_s Unit (fun '(x, (v,_)) _ => (x :: v, tt));
  snoc n o := fun_s Unit (fun '(v, (x,_)) _ => ( 
    let v' := (v ++ [x]) 
    in match Nat.eq_dec (n + 1) (S n)  with 
      | left Heq => rew [fun x => denote_kind (Vector o x)] Heq in v'
      | right Hneq => (ltac:(exfalso; lia))
      end, tt));
  uncons n o := fun_s Unit (fun '(v,_) _ => ((hd v, tl v), tt));
  unsnoc n o := fun_s Unit (fun v _ => (
    let v' := match Arith.Compare_dec.le_dec n (S n)  with 
      | left Hlt => take n Hlt (fst v)
      | right Hnlt => (ltac:(exfalso; lia))
      end in
    (v', last (fst v)), tt));
  concat n m o := fun_s Unit (fun '(x, (y, _)) _ => (Vector.append x y, tt));

  split n m o := fun_s Unit (fun x _ => (Vector.splitat n (fst x), tt));

  slice n x y o H1 H2 := fun_s Unit (fun v _ => (
    match Nat.eq_dec n (y + (n - y)) with 
      | left Heq =>
        let '(_, v) := splitat y (rew [fun x => Vector.t (denote_kind o) x] Heq in (fst v))
        in 
          match Nat.eq_dec (n-y) ((x - y + 1) + (n - x - 1)) with 
          | left Heq => _
          | right Hneq => (ltac:(exfalso;lia))
          end
      | right Hneq => (ltac:(exfalso;lia))
      end, tt));
}.
Proof.
  (* slice *)
  - cbn.
    intros.
    rewrite Heq in v.
    apply (splitat (x-y+1)) in v.
    apply (fst) in v.
    exact v.
Defined.

End instance.

Local Open Scope category_scope.

Inductive kind_only_units: Kind -> Prop :=
| OnlyUnitsTuple: forall l r, kind_only_units l -> kind_only_units r -> kind_only_units (Tuple l r)
| OnlyUnitsUnit: kind_only_units Unit
| OnlyUnitsVector: forall ty n, kind_only_units ty -> kind_only_units (Vector ty n).

Definition has_no_state {x y} (circuit: x ~[EvalCava]~> y) :=
  kind_only_units (evalProjState circuit).

Lemma has_no_state_compose: forall x y z (f: x~>y) (g: y~>z), 
  has_no_state f ->
  has_no_state g ->
  has_no_state (f >>> g) .
Proof.
  intros.
  constructor.
  apply H.
  apply H0.
Qed.

(*TODO: Is the sumbool actually computable? If not, is this still useful? *)
Definition has_no_state_dec {x y} (circuit: x ~[EvalCava]~> y): {has_no_state circuit} + {~has_no_state circuit}.
Proof.
  cbv [has_no_state].
  set (s:=evalProjState circuit).
  induction s; cbn in *; auto.

  inversion IHs1.
  inversion IHs2.
  * left. refine (OnlyUnitsTuple _ _ _ _); auto.
  * right. 
    unfold not in *.
    intros.
    inversion H1.
    apply H0 in H5.
    inversion H5.
  * right. 
    unfold not in *.
    intros.
    inversion H0.
    apply H in H3.
    inversion H3.
  * left. exact OnlyUnitsUnit.
  * right. unfold not. intros. inversion H.
  * inversion IHs.
    left. exact (OnlyUnitsVector _ _ H).
    right. unfold not in *. intros. inversion H0. apply H in H2. inversion H2.
Defined.

Lemma only_units_is_singular: forall ty,
  kind_only_units ty -> 
  (forall s:denote_kind ty, s = kind_default ty).
Proof.
  intros.
  induction ty; simpl in *.
  - inversion H.
    destruct s.
    apply IHty1 with (s:= d) in H2.
    apply IHty2 with (s:= d0) in H3.
    rewrite H2.
    rewrite H3.
    reflexivity.
  - induction s. reflexivity.
  - induction s. inversion H. reflexivity.
  - induction s; auto.
    simpl.
    f_equal.
    inversion H.
    apply IHty with (s:=h) in H1.
    apply H1.
    apply IHs.
    inversion H.
    exact (OnlyUnitsVector _ _ H1).
Qed.

Lemma state_is_irrelevant_for_stateless_circuit: forall {x y} 
  (circuit: x ~[EvalCava]~> y) ,
  has_no_state circuit -> 
  (forall s:denote_kind (evalProjState circuit), s = kind_default (projT1 circuit)).
Proof.
  intros.
  unfold has_no_state in H.
  apply only_units_is_singular with (s:=s) in H.
  exact H.
Qed.

Definition evaluate {X Y} (circuit: X ~[EvalCava]~> Y)
  (x: denote_kind X)
  (state: denote_kind (evalProjState circuit))
  : (denote_kind Y * denote_kind (evalProjState circuit)) :=
  ((projT2 circuit) x state).

Definition stateless_evaluation {X Y} (circuit: X ~[EvalCava]~> Y)
  (H: has_no_state circuit) (x: denote_kind X): denote_kind Y
  :=
  fst ((projT2 circuit) x (kind_default _)).

(* Given any explicit state, 'stateless_evaluation' computes the same
result. *)
Lemma different_state_same_result_for_stateless:
  forall {X Y} (circuit: X ~[EvalCava]~> Y) (H: has_no_state circuit),
  forall state x, stateless_evaluation circuit H x = fst (evaluate circuit x state).
Proof.
  intros.
  unfold stateless_evaluation, evaluate.
  repeat f_equal.
  apply (state_is_irrelevant_for_stateless_circuit circuit) with (s:=state) in H.
  rewrite H.
  reflexivity.
Qed.
  
Hint Extern 5 (has_no_state ?X) =>
  (match_primitive X; constructor) + (match_compose X; apply has_no_state_compose)
  : stateless.

Hint Extern 6 (has_no_state _) =>
  match goal with
  | [H: has_no_state ?Y |- has_no_state ?Y] => apply H
  end : stateless.

Hint Extern 5 (has_no_state (remove_rightmost_tt _)) =>
  constructor : stateless.

Example not_gate_is_stateless: has_no_state (not_gate).
Proof. auto with stateless. Qed.

Example evaluate_not_true: evaluate not_gate (true, tt) tt = (false, tt).
Proof. reflexivity. Qed.

Example evaluate_not_true_with_stateless: 
  stateless_evaluation not_gate not_gate_is_stateless (true, tt) = false.
Proof. reflexivity. Qed.

(* The proof is not 'forall x, ~ has_no_state ...' as a delay_gate of a unit type 
has no state as unit types are stateless by definition *)
Example delay_gate_is_stateful: exists x, ~ has_no_state (delay_gate (o:=x)).
Proof. 
  cbv [has_no_state not]. 
  simpl. 
  eexists. 
  intros.
  instantiate (1:=Bit) in H.
  inversion H.
Qed.

Example evaluate_delay_gate: evaluate (delay_gate (o:=Bit)) (true, tt) false = (false, true).
Proof. reflexivity. Qed.