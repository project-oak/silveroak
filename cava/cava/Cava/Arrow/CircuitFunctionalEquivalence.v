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

From coqutil Require Import Tactics.Tactics.
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

  | Uncancell_equiv: forall x r,
    (forall a, r a = (tt, a)) ->
    circuit_equiv x (Tuple Unit x) (Structural (Uncancell x)) r
  | Uncancelr_equiv: forall x r,
    (forall a, r a = (a, tt)) ->
    circuit_equiv x (Tuple x Unit) (Structural (Uncancelr x)) r

  | Cancell_equiv: forall x r,
    (forall a, r a = @snd _ (denote_kind x) a) ->
    circuit_equiv (Tuple Unit x) x (Structural (Cancell x)) r
  | Cancelr_equiv: forall x r,
    (forall a, r a = @fst (denote_kind x) _ a) ->
    circuit_equiv (Tuple x Unit) x (Structural (Cancelr x)) r

  | First_equiv: forall x y z c r r1,
    circuit_equiv x y c r1 ->
    (forall a : denote_kind x * denote_kind z, r a = (r1 (fst a), snd a)) ->
    circuit_equiv (Tuple x z) (Tuple y z) (First x y z c) r

  | Second_equiv: forall x y z c r r1,
    circuit_equiv x y c r1 ->
    (forall a : denote_kind z * denote_kind x, r a = (fst a, r1 (snd a))) ->
    circuit_equiv (Tuple z x) (Tuple z y) (Second x y z c) r

  | Swap_equiv: forall x y r,
    (forall a : denote_kind x * denote_kind y, r a = (snd a, fst a)) ->
    circuit_equiv (Tuple x y) (Tuple y x) (Structural (Swap x y)) r
  | Drop_equiv: forall x r,
    (forall a, r a = tt) ->
    circuit_equiv x Unit (Structural (Drop x)) r
  | Copy_equiv: forall x r,
    (forall a, r a = (a,a)) ->
    circuit_equiv x (Tuple x x) (Structural (Copy x)) r

  | Assoc_equiv: forall x y z r,
    (forall i : denote_kind x * denote_kind y * denote_kind z,
      r i = (fst (fst i), (snd (fst i), snd i))) ->
    circuit_equiv (Tuple (Tuple x y) z) (Tuple x (Tuple y z))
    (Structural (Assoc x y z)) r
  | Unassoc_equiv: forall x y z r,
    (forall i : denote_kind x * (denote_kind y * denote_kind z),
      r i = ((fst i, fst (snd i)), snd (snd i))) ->
    circuit_equiv (Tuple x (Tuple y z)) (Tuple (Tuple x y) z)
    (Structural (Unassoc x y z)) r

  | Id_equiv: forall x r,
    (forall a, r a = a) ->
    circuit_equiv x x (Structural (Arrow.Id x)) r

  | Map_equiv: forall x y n c r r1,
    circuit_equiv x y c r1 ->
    (forall v, r v = Vector.map r1 v) ->
    circuit_equiv (Vector x n) (Vector y n) (Map x y n c) r

  | Resize_equiv: forall x n nn r,
    (forall v, r v = resize_default (kind_default _) nn v) ->
    circuit_equiv (Vector x n) (Vector x nn) (Resize x n nn) r

  | Primtive_equiv: forall p r,
    (forall a, r a = combinational_evaluation' (CircuitArrow.Primitive p) a) ->
    circuit_equiv (primitive_input p) (primitive_output p)
                  (CircuitArrow.Primitive p) r

  (* | Any_equiv: forall i o c, *)
  (*   circuit_equiv i o c (combinational_evaluation' c) *)
.

Lemma circuit_equiv_ext {i o} c spec1 spec2 :
  (forall x, spec1 x = spec2 x) -> circuit_equiv i o c spec1 ->
  circuit_equiv i o c spec2.
Proof.
  intro Hspec; induction 1.
  all:(econstructor; eauto; [ ]).
  all:intros; rewrite <-Hspec; eauto.
Qed.

Lemma circuit_equiv_implies_combinational_evaluation' {i o} c spec :
  circuit_equiv i o c spec ->
  (forall input : denote_kind i, spec input = combinational_evaluation' c input).
Proof.
  induction 1; cbn [combinational_evaluation' denote_kind]; intros.
  all: repeat match goal with
              | Hr : forall a, ?r a = _ |- _ => rewrite Hr
              end.
  all:destruct_products; cbn [fst snd].
  all:eauto using Vector.map_ext.
Qed.

Lemma circuit_equiv_combinational_evaluation' {i o} c :
  circuit_equiv i o c (combinational_evaluation' c).
Proof.
  induction c; cbn [combinational_evaluation']; intros.
  all:try match goal with
          | x : ArrowStructure |- _ => destruct x
          | x : CircuitPrimitive |- _ => destruct x
          end.
  all:try econstructor; eauto.
  all:intros; destruct_products; eauto.
  (* TODO: loop cases missing *)
Abort.

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

Ltac arrowsimpl :=
  cbn [cancell cancelr uncancell uncancelr assoc unassoc first second copy drop
               swap compose CircuitCat CircuitArrow CircuitArrowSwap
               CircuitArrowDrop CircuitArrowCopy arrow_category as_kind
               Datatypes.length Nat.eqb extract_nth rewrite_or_default ].

(* Add [obeys_spec] proofs to this hint database, and circuit_spec will use
   them *)
Create HintDb circuit_spec_correctness discriminated.

Ltac circuit_spec_step :=
  lazymatch goal with
  | |- ?lhs = ?rhs =>
    cbn [Datatypes.fst Datatypes.snd];
    instantiate_app_by_reflexivity
  | |- circuit_equiv _ _ ?c _ =>
    lazymatch c with
    | closure_conversion' _ _ =>
      apply obeys_spec_to_circuit_equiv;
      solve [eauto with circuit_spec_correctness]
    | _ => first [ econstructor; intros
                | solve [eauto with circuit_spec_correctness] ]
    end
  | |- ?x => fail "Stuck at" x
  end.
Ltac circuit_spec :=
  cbv [obeys_spec]; cbn [closure_conversion']; arrowsimpl;
  repeat circuit_spec_step; cbn [denote_kind combinational_evaluation' fst snd].

