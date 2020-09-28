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

From Arrow Require Import Category Arrow.
From Cava.Arrow Require Import ArrowKind CircuitArrow CircuitSemantics
     ExprSyntax ExprLowering.
Require Import Cava.Tactics Cava.VectorUtils.

Inductive circuit_equiv: forall i o, Circuit i o -> (denote_kind i -> denote_kind o) -> Prop :=
  | Composition_equiv: forall x y z c1 c2 r1 r2 r,
    circuit_equiv x y c1 r1 ->
    circuit_equiv y z c2 r2 ->
    (forall a:denote_kind x, r a = r2 (r1 a) ) ->
    circuit_equiv x z (Composition _ _ _ c1 c2) r

  | Uncancell_equiv: forall x,
    circuit_equiv x (Tuple Unit x) (Structural (Uncancell x)) (fun a => (tt, a))
  | Uncancelr_equiv: forall x,
    circuit_equiv x (Tuple x Unit) (Structural (Uncancelr x)) (fun a => (a, tt))

  | Cancell_equiv: forall x,
    circuit_equiv (Tuple Unit x) x (Structural (Cancell x)) (fun a => snd a)
  | Cancelr_equiv: forall x,
    circuit_equiv (Tuple x Unit) x (Structural (Cancelr x)) (fun a => fst a)

  | First_equiv: forall x y z c r r1,
    circuit_equiv x y c r1 ->
    (forall a, r a = (r1 (fst a), snd a)) ->
    circuit_equiv (Tuple x z) (Tuple y z) (First x y z c) r

  | Second_equiv: forall x y z c r r1,
    circuit_equiv x y c r1 ->
    (forall a, r a = (fst a, r1 (snd a))) ->
    circuit_equiv (Tuple z x) (Tuple z y) (Second x y z c) r

  | Swap_equiv: forall x y,
    circuit_equiv (Tuple x y) (Tuple y x) (Structural (Swap x y)) (fun a => (snd a, fst a))
  | Drop_equiv: forall x,
    circuit_equiv x Unit (Structural (Drop x)) (fun a => tt)
  | Copy_equiv: forall x,
    circuit_equiv x (Tuple x x) (Structural (Copy x)) (fun a => (a,a))

  | Assoc_equiv: forall x y z,
    circuit_equiv (Tuple (Tuple x y) z) (Tuple x (Tuple y z))
    (Structural (Assoc x y z)) (fun i => (fst (fst i), (snd (fst i), snd i)))
  | Unassoc_equiv: forall x y z,
    circuit_equiv (Tuple x (Tuple y z)) (Tuple (Tuple x y) z)
    (Structural (Unassoc x y z)) (fun i => ((fst i, fst (snd i)), snd (snd i)))

  | Id_equiv: forall x,
    circuit_equiv x x (Structural (Arrow.Id x)) (fun a => a)

  | Map_equiv: forall x y n c r r1,
    circuit_equiv x y c r1 ->
    (forall v, r v = Vector.map r1 v) ->
    circuit_equiv (Vector x n) (Vector y n) (Map x y n c) r

  | Resize_equiv: forall x n nn,
    circuit_equiv (Vector x n) (Vector x nn) (Resize x n nn)
      (fun v => resize_default (kind_default _) nn v)

  | Primtive_equiv: forall p,
    circuit_equiv (primitive_input p) (primitive_output p) (CircuitArrow.Primitive p) (combinational_evaluation' (CircuitArrow.Primitive p))

  (* | Any_equiv: forall i o c, *)
  (*   circuit_equiv i o c (combinational_evaluation' c) *)
.

(* wrapper for circuit_equiv that keeps goals in standard, recursion-friendly form *)
Definition obeys_spec {i o}
           (c : @morphism Kind KappaCat i o)
           (spec : denote_kind i -> denote_kind o) :=
  circuit_equiv _ _ (closure_conversion' Datatypes.nil (c natvar))
                (fun (x : denote_kind (i ** as_kind Datatypes.nil)%Arrow) =>
                   spec (Datatypes.fst x)).

(* this lemma helps get a subcircuit goal into the [obeys_spec] form so eauto
   recognizes it *)
Lemma obeys_spec_to_circuit_equiv i o c spec :
  @obeys_spec i o c spec ->
  circuit_equiv _ _ (closure_conversion' Datatypes.nil (c natvar))
                (fun x => spec (Datatypes.fst x)).
Proof. intro H; exact H. Qed.

Hint Unfold cancell cancelr uncancell uncancelr assoc unassoc first second
     copy drop swap compose
     CircuitCat CircuitArrow CircuitArrowSwap CircuitArrowDrop CircuitArrowCopy
     arrow_category as_kind Datatypes.length Nat.eqb extract_nth
     rewrite_or_default
  : arrowunfold.

Ltac circuit_spec_step :=
  lazymatch goal with
  | |- ?lhs = ?rhs =>
    cbn [Datatypes.fst Datatypes.snd];
    instantiate_app_by_reflexivity
  | |- circuit_equiv _ _ ?c _ =>
    lazymatch c with
    | closure_conversion' _ _ =>
      (* subcircuit *)
      apply obeys_spec_to_circuit_equiv;
      solve [eauto with circuit_spec_correctness]
    | _ => econstructor; intros
    end
  | |- ?x => fail "Stuck at" x
  end.
Ltac circuit_spec :=
  cbv [obeys_spec]; cbn [closure_conversion']; autounfold with arrowunfold;
  repeat circuit_spec_step; cbn [denote_kind combinational_evaluation' fst snd].

