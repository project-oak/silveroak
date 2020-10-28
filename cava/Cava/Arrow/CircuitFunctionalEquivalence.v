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
From Cava Require Import Arrow.Classes.Category.
From Cava Require Import Arrow.Classes.Arrow.
From Cava Require Import Arrow.Primitives.
From Cava.Arrow Require Import ArrowKind CircuitArrow CircuitProp
     CircuitSemantics ExprSyntax ExprLowering.
Require Import Cava.Tactics Cava.VectorUtils.

Inductive circuit_equiv: forall i o, Circuit i o -> (denote_kind i -> denote_kind o) -> Prop :=
  | Composition_equiv: forall x y z c1 c2 r1 r2 r,
    circuit_equiv x y c1 r1 ->
    circuit_equiv y z c2 r2 ->
    (forall a:denote_kind x, r a = r2 (r1 a)) ->
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

  | RewriteTy_equiv: forall x y r,
    (forall v, r v = rewrite_or_default x y v) ->
    circuit_equiv x y (RewriteTy x y ) r

  | Primitive_equiv: forall p r,
    (forall a, r a = combinational_evaluation' (CircuitArrow.Primitive p) a) ->
    circuit_equiv _ _
                  (CircuitArrow.Primitive p) r
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
  is_combinational c ->
  circuit_equiv i o c (combinational_evaluation' c).
Proof.
  induction c; cbn [combinational_evaluation']; intros.
  all:try match goal with
          | x : ArrowStructure |- _ => destruct x
          | x : CircuitPrimitive |- _ => destruct x
          end.
  all:try econstructor; eauto.
  all:intros; destruct_products; eauto.
  all:cbv [is_combinational] in *; cbn [no_loops no_delays] in *.
  all:repeat match goal with
             | H : (_ && _)%bool = true |- _ =>
               apply Bool.andb_true_iff in H; destruct H
             | _ => discriminate
             end.
  all: eauto using Bool.andb_true_iff.
Qed.

(* wrapper for circuit_equiv that keeps goals in standard, recursion-friendly form *)
Definition obeys_spec {i o}
           (c : @morphism Kind KappaCat i o)
           (spec : denote_kind i -> denote_kind o) :=
  circuit_equiv _ _ (closure_conversion' Datatypes.nil (c natvar))
                (fun (x : denote_kind i * unit) =>
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

Ltac circuit_spec_instantiate :=
  lazymatch goal with
  | |- _ = _ =>
    cbn [fst snd denote_kind product primitive_output];
    lazymatch goal with
    | |- context [combinational_evaluation' (CircuitArrow.Primitive _)] =>
      (* simplify combinational_evaluation' if there's a primitive *)
      cbv [combinational_evaluation' primitive_interp]
    | |- _ = @resize_default _ ?n ?d ?n ?v =>
      (* change resize_default to identity function if it appears *)
      transitivity v; [ | rewrite resize_default_id; reflexivity ]
    | |- _ = Vector.map (fun x => x) ?v =>
      (* change Vector.map id to identity function if it appears *)
      transitivity v; [ | rewrite Vector.map_id; reflexivity ]
    | _ => idtac
    end; cbn[fst snd denote_kind product primitive_output];
    instantiate_app_by_reflexivity
  end.

Ltac lower1 :=
  lazymatch goal with
  | |- circuit_equiv _ _ (@closure_conversion' ?t1 ?t2 ?ctxt ?k) _ =>
    lazymatch k with
    | @Abs _ ?x ?y ?z ?f =>
      (* sometimes the types need to be coerced for Abs *)
      first [ rewrite (@lower_abs x y z f ctxt)
            | change t1 with (Tuple x y); change t2 with z;
              rewrite (@lower_abs x y z f ctxt) ]
    | @App _ ?x ?y ?z ?f ?e => rewrite (@lower_app x y z f e ctxt)
    | @Let _ ?x ?y ?z ?v ?f => rewrite (@lower_let x y z f v ctxt)
    | @RemoveContext _ ?x ?y ?e =>
      first [ rewrite (@lower_remove_context x y e ctxt)
            | change x with t1; change y with t2;
              rewrite (@lower_remove_context t1 t2 e ctxt) ]
    | @Comp _ ?x ?y ?z ?e1 ?e2 =>
      rewrite (@lower_comp x y z e2 e1 ctxt)
    | @Primitive _ ?p => cbv [closure_conversion']
    | @Var _ _ _ => cbv [closure_conversion']
    end; arrowsimpl
  end.

Ltac primitive_equiv :=
  lazymatch goal with
  | |- circuit_equiv ?x ?y (CircuitArrow.Primitive ?p) _ =>
    change x with (primitive_input p);
    change y with (primitive_output p);
    eapply Primitive_equiv; intros
  end.

Ltac circuit_spec_step :=
  lazymatch goal with
  | |- circuit_equiv _ _ (closure_conversion' _ ?c) _ =>
    first [ lower1
          | apply obeys_spec_to_circuit_equiv;
            solve [eauto with circuit_spec_correctness ] ]
  | |- circuit_equiv _ _ _ _ =>
    first [ econstructor; intros
          | solve [ eauto with circuit_spec_correctness ]
          | primitive_equiv ]
  | |- ?lhs = ?rhs => circuit_spec_instantiate
  | |- ?x => fail "Stuck at" x
  end.

Ltac circuit_spec :=
  cbv [obeys_spec]; cbn [primitive_input primitive_output as_kind];
  repeat circuit_spec_step; cbn [denote_kind product fst snd]; fold denote_kind.

(* Version of [circuit_spec] that expects to solve the goal *)
Ltac circuit_spec_crush :=
  circuit_spec; autorewrite with vsimpl; repeat destruct_pair_let;
  repeat match goal with
         | u : unit |- _ => destruct u
         | |- context [@snd _ unit ?x] => destruct (snd x)
         | |- context [@fst unit _ ?x] => destruct (fst x)
         end;
  (reflexivity || instantiate_app_by_reflexivity).
