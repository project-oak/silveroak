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

(* temporarily disabled *)
(* From Arrow Require Import Category Arrow Kappa ClosureConversion.
From Cava Require Import Arrow.CavaArrow Arrow.EvaluationArrow Arrow.CavaExpression.

From Coq Require Import Arith NArith Lia NaryFunctions.

Import EqNotations.

Open Scope category_scope.
Open Scope arrow_scope.

(* TODO: This is defined in the standard library but P is restricted to `A -> Prop`:
  upstream fix to github.com/coq/coq *)
Lemma rew_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Type) (u : { p : P x & Q x p }) {y} (H : x = y)
    : rew [fun a => { p : P a & Q a p }] H in u
      = existT
          (Q y)
          (rew H in projT1 u)
          (match H with 
          | eq_refl => projT2 u
          end).
Proof.
  destruct H, u; reflexivity.
Qed.

Lemma blank_rew: forall ty ty' H x, eq_rect ty (fun (_ : Kind) => Kind) x ty' H = x.
Proof.
  intros.
  destruct H.
  simpl.
  reflexivity.
Qed.

From Coq Require Import Program.Equality.

(* TODO: It should be possible to generalize these for all arrows/kappa,
but the proofs are more difficult and may require additional hypothesis which are 
implicit here, such as '**' being injective. *)
Lemma morph_prop_abs_inj: forall {x y z k a},
  MorphPropKappa natvar (fun _ _ => has_no_state) (x ** y) z (Kappa.Abs natvar x k) -> 
  MorphPropKappa natvar (fun _ _ => has_no_state) y z (k a).
Proof.
  intros.
  dependent induction H.
  apply H.
Qed.

Lemma no_let_rec_abs_inj: forall {x y z k a},
  NoLetRecKappa (A0:=EvalCava) natvar (x ** y) z (Kappa.Abs natvar x k) ->
  NoLetRecKappa natvar y z (k a).
Proof.
  intros.
  dependent induction H.
  apply H.
Qed.

Lemma morph_prop_app_inj: forall {x y z f e},
  MorphPropKappa natvar (fun _ _ => has_no_state) y z (Kappa.App natvar f e) -> 
  MorphPropKappa natvar (fun _ _ => has_no_state) (x**y) z f /\
  MorphPropKappa natvar (fun _ _ => has_no_state) u x e.
Proof.
  intros.
  dependent induction H.
  split.
  apply H.
  apply H0.
Qed.

Lemma no_let_rec_app_inj: forall {x y z f e},
  NoLetRecKappa (A0:=EvalCava) natvar y z (Kappa.App natvar f e) -> 
  NoLetRecKappa natvar (x**y) z f /\
  NoLetRecKappa natvar u x e.
Proof.
  intros.
  dependent induction H.
  split.
  apply H.
  apply H0.
Qed.

Lemma morph_prop_comp_inj: forall {x y z e1 e2},
  MorphPropKappa natvar (fun _ _ => has_no_state) x z (Kappa.Comp natvar e1 e2) -> 
  MorphPropKappa natvar (fun _ _ => has_no_state) y z e1 /\
  MorphPropKappa natvar (fun _ _ => has_no_state) x y e2.
Proof.
  intros.
  dependent induction H.
  split.
  apply H.
  apply H0.
Qed.

Lemma no_let_rec_comp_inj: forall {x y z e1 e2},
  NoLetRecKappa (A0:=EvalCava) natvar x z (Kappa.Comp natvar e1 e2) -> 
  NoLetRecKappa natvar y z e1 /\
  NoLetRecKappa natvar x y e2.
Proof.
  intros.
  dependent induction H.
  split.
  apply H.
  apply H0.
Qed.

Lemma morph_prop_morph_inj: forall {x y m},
  MorphPropKappa natvar (fun _ _ => has_no_state) x y (Kappa.Morph natvar m) -> 
  has_no_state m.
Proof.
  intros.
  dependent induction H.
  apply H.
Qed.

Lemma no_let_rec_and_stateless_morphisms_is_stateless:
  forall i o (expr: kappa natvar i o) env wf, 
    NoLetRecKappa natvar i o expr ->
    MorphPropKappa natvar (fun _ _ m => has_no_state m) i o expr ->
    has_no_state ((fun (cava: Cava) => closure_conversion' (object_decidable_equality:=eq_kind_dec) env expr wf) EvalCava).
Proof.
  intros. 
  simpl.

  apply (kappa_ind natvar (fun o0 o1 expr => 
    forall env,
    forall wf: wf_debrujin env expr, 
    NoLetRecKappa natvar o0 o1 expr ->
    MorphPropKappa natvar (fun _ _ m => has_no_state m) o0 o1 expr ->
    has_no_state
    (closure_conversion' (arrow:=EvalCava) env expr wf)));
  intros; unfold has_no_state; cbn.

  
  - (* Var case *)
    (* TODO: could this be simplified ? Discriminating on the environment
      works but may be more surgical than necessary. *)
    induction env0.
    inversion wf0.

    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    apply wf_debrujin_var_succ in wf0 as wf1.
    inversion wf1.
    simpl.
    inversion H1.
    apply lookup_bound in H3.
    destruct (Nat.eq_dec v (length env0)).
    * exfalso; lia.
    * apply IHenv0.
    * simpl.
      destruct (Nat.eq_dec v (length env0)).
      destruct (eq_kind_dec a y).
      unfold evalProjState.
      
      unfold evalMorphism.
      setoid_rewrite
        (rew_sigT (P:=(fun _ => Kind))
        (fun y state => denote a * denote (as_kind env0) -> denote state -> denote y * denote state)
        _ 
        e0).
      simpl.
      rewrite blank_rew.
      refine (OnlyUnitsTuple _ _ OnlyUnitsUnit OnlyUnitsUnit).
      destruct (lookup_top_contra env0 e wf0 n).
      simpl.
      apply IHenv0.

  - (* Abs case *)
    simpl in *.
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).

    apply (H1 (length env0) (List.cons x env0) (wf_debrujin_succ k wf0)).
    apply (no_let_rec_abs_inj H2).
    apply (morph_prop_abs_inj H3).

  - (* App case *)
    simpl in *.
    pose (no_let_rec_app_inj H3) as H5.
    pose (morph_prop_app_inj H4) as H6.
    inversion H5.
    inversion H6.
    refine (OnlyUnitsTuple _ _ _ _).
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    apply (H2 _ _ H8 H10).
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    apply (H1 _ _ H7 H9).
  
  - (* Comp case *)
    simpl in *.
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    pose (no_let_rec_comp_inj H3) as H5.
    pose (morph_prop_comp_inj H4) as H6.
    inversion H5.
    inversion H6.
    refine (OnlyUnitsTuple _ _ _ _).
    apply (H2 _ _ H8 H10).
    apply (H1 _ _ H7 H9).
  
  - (* Morph case *)
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _).
    apply (morph_prop_morph_inj H2).

  - (* LetRec case *)
    inversion H3.

  - apply H.
  - apply H0.
Qed.

Hint Extern 15 => apply (no_let_rec_and_stateless_morphisms_is_stateless _ _) : stateless.
Hint Extern 20 => refine (OnlyUnitsTuple _ _ OnlyUnitsUnit _ ) : stateless. *)