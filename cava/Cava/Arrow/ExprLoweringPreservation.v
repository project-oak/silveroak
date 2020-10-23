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

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Arrow.Classes.Arrow.
Require Import Cava.Arrow.Classes.Category.
Require Import Arrow.CircuitArrow.
Require Import Cava.Arrow.ArrowKind.
Require Import Cava.Arrow.CircuitProp.
Require Import Cava.Arrow.CircuitSemantics.
Require Import Cava.Arrow.ExprEquiv.
Require Import Cava.Arrow.ExprLowering.
Require Import Cava.Arrow.ExprSemantics.
Require Import Cava.Arrow.ExprSyntax.

(* TODO: this is copied from CircuitFunctionalEquivalence and extended; it
   should be moved to a more general location *)
Local Ltac arrowsimpl :=
  cbn [cancell cancelr uncancell uncancelr assoc unassoc first second compose
    Arrows.copy Arrows.drop Arrows.loopr Arrows.loopl Arrows.swap compose id
    Arrows.rewrite_or_default rewrite_or_default
    combinational_category combinational_arrow
    combinational_drop combinational_copy combinational_swap
    combinational_arrow_rewrite_or_default
    Coq.build_denoted_category Coq.build_denoted_arrow
    arrow_category rewrite_or_default as_kind
    Datatypes.length Nat.eqb extract_nth
    ].

Lemma rewrite_or_default_refl A x :
  rewrite_or_default A A x = x.
Proof.
  induction A; cbn [rewrite_or_default] in *; arrowsimpl;
    cbn [fst snd]; autorewrite with vsimpl;
      try reflexivity; [ ].
  destruct_one_match; rewrite IHA1, IHA2; eauto using surjective_pairing.
Qed.

Definition context_entry_ok
           (ctxt_types : list Kind)
           (ctxt_values : denote_kind (as_kind ctxt_types))
           (e : { t : Kind & (coq_func t * natvar t)%type})
  : Prop :=
  let value := fst (projT2 e) in
  let index := snd (projT2 e) in
  reverse_nth ctxt_types index = Some (projT1 e) /\
  (extract_nth (arrow:=combinational_arrow) ctxt_types _ index) ctxt_values = value.

Lemma extend_context_entry_ok_tl ctxt_types ctxt t (x : denote_kind t) e :
  context_entry_ok ctxt_types ctxt e ->
  context_entry_ok (t :: ctxt_types) (x, ctxt) e.
Proof.
  cbv [context_entry_ok]; intros.
  repeat match goal with
         | x : { _ & _ } |- _ => destruct x
         | x : _ * _ |- _ => destruct x
         | H : _ /\ _ |- _ => destruct H
         | _ => progress cbn [projT1 projT2 fst snd rev] in *
         end.
  erewrite split_lookup by eauto.
  split; [ reflexivity | ].
  cbn [extract_nth].
  destruct_one_match; arrowsimpl; cbn [fst snd];
    subst; [ | tauto ].

  match goal with
  | H : reverse_nth _ (length _) = Some _ |- _ =>
    apply lookup_upper_contra in H
  end.
  tauto.
Qed.

Lemma extend_context_entry_ok_hd ctxt_types ctxt t (x : denote_kind t) :
  context_entry_ok (t :: ctxt_types) (x, ctxt) (vars _ _ (x, length ctxt_types)).
Proof.
  cbv [context_entry_ok]. fold as_kind denote_kind in *.
  cbn [rev projT1 projT2 fst snd vars].
  erewrite split_lookup by eauto.
  split; [ reflexivity | ]. cbn [extract_nth].
  destruct_one_match; arrowsimpl; [ | tauto ].
  cbn [fst snd]. apply rewrite_or_default_refl.
Qed.

Fixpoint no_letrec {var i o} (e : kappa var i o) : Prop :=
  match e with
  | Var _ => True
  | Abs f => forall v, no_letrec (f v)
  | App f x => no_letrec f /\ no_letrec x
  | Comp e1 e2 => no_letrec e1 /\ no_letrec e2
  | Primitive _ => True
  | Let x f => no_letrec x /\ forall v, no_letrec (f v)
  | LetRec _ _ => False
  | Id => True
  | RemoveContext e => no_letrec e
  | Module _ f => no_letrec f
  end.
Definition NoLetRec {i o} (e : Kappa i o) : Prop := no_letrec (e unitvar).

Lemma no_letrec_unitvar_equiv
      i o var (expr1 : kappa unitvar i o) (expr2 : kappa var i o) G :
  kappa_equivalence G expr1 expr2 ->
  no_letrec expr1 ->
  no_letrec expr2.
Proof.
  induction 1; intros; cbn [no_letrec] in *; destruct_products; solve [eauto].
  Unshelve. all: apply tt.
Qed.

Lemma closure_conversion'_preserves_semantics i o :
  forall (expr1 : kappa coq_func i o) (expr2 : kappa natvar i o) G,
    kappa_equivalence G expr1 expr2 ->
    no_letrec expr1 ->
    forall (ctxt_types : list Kind) (ctxt : denote_kind (as_kind ctxt_types))
      (x : denote_kind i),
      Forall (context_entry_ok ctxt_types ctxt) G ->
      interp_combinational' expr1 x
      = (closure_conversion' (arrow:=combinational_arrow) ctxt_types expr2) (x, ctxt).
Proof.
  induction 1; intros.
  all:cbn [interp_combinational' closure_conversion'].
  all:cbn [denote_kind no_letrec] in *; destruct_products.
  all:arrowsimpl; cbn [fst snd].
  { (* Var *)
    match goal with
    | HForall : Forall ?P ?l, HIn : In ?x ?l |- _ =>
      let H := fresh in
      assert (H : P x) by (eapply Forall_forall; eauto);
        destruct H as [? ?]
    end.
    cbn [vars projT1 projT2 fst snd] in *.
    congruence. }
  { (* Abs *)
    match goal with
    | IH : _ |- _ => erewrite IH with (ctxt_types:=_ :: ctxt_types)
    end; [ reflexivity | solve [eauto] | ].
    apply Forall_cons; [ solve [apply extend_context_entry_ok_hd] | ].
    eapply Forall_impl; [ | eassumption].
    apply extend_context_entry_ok_tl. }
  { (* App *)
    erewrite IHkappa_equivalence1, IHkappa_equivalence2 by eauto.
    reflexivity. }
  { (* Comp *)
    erewrite IHkappa_equivalence1, IHkappa_equivalence2 by eauto.
    reflexivity. }
  { (* Primitive *) reflexivity. }
  { (* Let *)
    erewrite IHkappa_equivalence by eauto.
    match goal with
    | IH : _ |- _ => erewrite IH with (ctxt_types:=_ :: ctxt_types)
    end; [ reflexivity | solve [eauto] | ].
    apply Forall_cons; [ solve [apply extend_context_entry_ok_hd] | ].
    eapply Forall_impl; [ | eassumption].
    apply extend_context_entry_ok_tl. }
  { (* LetRec *) tauto. }
  { (* Id *) reflexivity. }
  { (* RemoveContext *)
    erewrite IHkappa_equivalence with (ctxt_types:=nil); eauto. }
Qed.

Theorem closure_conversion_preserves_semantics i o (expr : Kappa i o) x :
  Wf expr -> NoLetRec expr ->
  interp_combinational (expr coq_func) x = combinational_evaluation expr x.
Proof.
  cbv [Wf interp_combinational combinational_evaluation closure_conversion].
  intros; arrowsimpl;
  eapply closure_conversion'_preserves_semantics with (ctxt_types:=nil) (G:=nil);
    eauto using Forall_nil, no_letrec_unitvar_equiv.
Qed.
