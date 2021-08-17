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

(* substitutes lets in a goal *)
Ltac subst_lets :=
  repeat lazymatch goal with x := _ |- _ => subst x end.

Section SubstLetsTests.
  Goal (forall (x : nat) (add:=Nat.add) (z:=x) (y:=add x z),
           0 < x + x -> 0 < y).
  Proof.
    intros. subst_lets.
    (* should now be fully substituted *)
    lazymatch goal with
    | |- 0 < x + x => idtac
    end.
    assumption.
  Qed.
End SubstLetsTests.

(* replaces an expression in the goal with the computed version of itself *)
Ltac compute_expr t :=
  let x := (eval compute in t) in
  change t with x.

Section ComputeExprTests.
  (* compute 2 * 16 *)
  Goal ((5 <= 2 * 16)).
  Proof.
    compute_expr (2 * 16).
    lazymatch goal with |- 5 <= 32 => idtac end.
    repeat apply le_n_S. apply le_0_n.
  Qed.

  (* selectively compute a subexpression *)
  Goal ((1 + (4 + 3) <= 2 * (4 + 3))).
  Proof.
    compute_expr (4 + 3).
    lazymatch goal with |- 1 + 7 <= 2 * 7 => idtac end.
    repeat apply le_n_S. apply le_0_n.
  Qed.
End ComputeExprTests.

(* The destruct_pair_let tactic finds "destructuring lets", e.g.

   let '(x, y) := p in ...

   These lets are actually matches under the hood; the above is equivalent to

   match p with | pair x y => ...  end

   This can be a problem because rewriting under matches is not allowed, even
   when the match has only one case. The destruct_pair_let tactic fixes the
   issue by changing p into (fst p, snd p), making the match disapper. *)
Ltac destruct_pair_let :=
  match goal with
  | |- context [ match ?p with pair _ _ => _ end ] =>
    rewrite (surjective_pairing p)
  end.

Section DestructPairLetTests.
  (* simple test *)
  Goal (forall x : nat * nat, let '(n, m) := x in n = fst x).
    intros.
    Fail reflexivity. (* reflexivity should not work yet because of match *)
    destruct_pair_let.
    reflexivity.
  Qed.

  (* many nested lets, same product destructed twice *)
  Goal (forall x : nat * nat * nat * nat,
           let '(a, b, c, d) := x in
           (c, a) = let '(n, m, p) := fst x in (p, n)).
    intros.
    repeat destruct_pair_let.
    reflexivity.
  Qed.
End DestructPairLetTests.

(* Helper for destruct_inner_pair_let *)
Ltac destruct_inner_pair_let' t :=
  lazymatch t with
  | context [ match ?p with
              | pair _ _ => _
              end ] =>
    first [ destruct_inner_pair_let' p
          | rewrite (surjective_pairing p) ]
  end.

(* Like destruct_pair_let, but destructs innermost lets first *)
Ltac destruct_inner_pair_let :=
  lazymatch goal with |- ?g => destruct_inner_pair_let' g end.

Section DestructInnerPairLetTests.
  (* simple test *)
  Goal (forall x : nat * nat, let '(n, m) := let (a,b) := x in (b,a) in n = snd x).
    intros.
    destruct_inner_pair_let. (* destructs x immediately *)
    reflexivity.
  Qed.
End DestructInnerPairLetTests.

(* Helper tactic for instantiate_lhs_app_by_reflexivity *)
Ltac app_head t :=
  lazymatch t with
  | ?f ?x => app_head f
  | ?f => f
  end.

(* Helper tactic for pattern_out_args *)
Ltac pattern_out_single_arg arg e :=
  lazymatch arg with
  | (?x, ?y) =>
    let eF := pattern_out_single_arg y e in
    let eF := pattern_out_single_arg x eF in
    constr:(fun xy => eF (fst xy) (snd xy))
  | ?x =>
    let eF := match (eval pattern x in e) with
              | ?f _ => f end in
    constr:(eF)
  end.

(* Helper tactic for instantiate_lhs_app_by_reflexivity *)
Ltac pattern_out_args term_with_args e :=
  lazymatch term_with_args with
  | ?f ?x =>
    let eF := pattern_out_single_arg x e in
    let eF := pattern_out_args f eF in
    constr:(eF)
  | ?f => constr:(e)
  end.

(* The instantiate_lhs_app_by_reflexivity tactic works on goals of the form:

   f x = g

   ... where f is an evar. It works by patterning out any occurences of [x] in
   the term [g] (i.e. changing [g] into an application of some function to [x])
   and then instantiating [f] with the resulting function. *)
Ltac instantiate_lhs_app_by_reflexivity :=
  lazymatch goal with
  | |- ?lhs = ?rhs =>
    let f := app_head lhs in
    is_evar f;
    let rhsF := pattern_out_args lhs rhs in
    let H := fresh in
    assert (rhsF = f) as H by reflexivity;
    clear H; reflexivity
  end.

(* Like instantiate_lhs_app_by_reflexivity, but expects the instantiatable
   function evar on the right-hand side of [=] (i.e. g = ?f x) *)
Ltac instantiate_rhs_app_by_reflexivity :=
  symmetry; instantiate_lhs_app_by_reflexivity.
(* instantiate_app_by_reflexivity is the top-level wrapper that tries calling
   both lhs and rhs versions *)
Ltac instantiate_app_by_reflexivity :=
  (instantiate_lhs_app_by_reflexivity
   || instantiate_rhs_app_by_reflexivity).

Section InstantiateAppByReflexivityTests.
  (* instantiate addition of 1 (rhs) *)
  Goal (exists f : nat -> nat, forall x, x + 1 = f x).
    eexists; intros.
    instantiate_app_by_reflexivity.
  Qed.

  (* instantiate addition of 1 (lhs) *)
  Goal (exists f : nat -> nat, forall x, x + 1 = f x).
    eexists; intros.
    instantiate_app_by_reflexivity.
  Qed.

  (* argument ignored *)
  Goal (exists f : nat -> nat, forall x, 2 = f x).
    eexists; intros.
    instantiate_app_by_reflexivity.
  Qed.

  (* argument has many occurences *)
  Goal (exists f : nat -> nat, forall x, f x = x + (2 * (x - 3) + x * x - x * 5)).
    eexists; intros.
    instantiate_app_by_reflexivity.
  Qed.

  (* two arguments *)
  Goal (exists f : nat -> nat -> nat, forall x y, f x y = x + (y * (x - 3) + y * x - x * 5)).
    eexists; intros.
    instantiate_app_by_reflexivity.
  Qed.

  (* two arguments, second ignored *)
  Goal (exists f : nat -> nat -> nat, forall x y, f x y = x + (2 * (x - 3) + x * x - x * 5)).
    eexists; intros.
    instantiate_app_by_reflexivity.
  Qed.

  (* Arguments paired on LHS and not on RHS *)
  Goal (exists f : nat * nat -> nat, forall x y, f (x,y) = x + (y * (x - 3) + y * x - x * 5)).
    eexists; intros.
    instantiate_app_by_reflexivity.
  Qed.

  (* Complex pairing *)
  Goal (exists f : nat * (nat * nat) * nat -> nat,
           forall w x y z, f (w,(x,y),z) = x + (w * (x - z) + y * x - x * (w + z))).
    eexists; intros.
    instantiate_app_by_reflexivity.
  Qed.
End InstantiateAppByReflexivityTests.

(* separate ands, exists, and projection equalities, without generating multiple
   goals *)
Ltac logical_simplify_step :=
  lazymatch goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : Some _ = Some _ |- _ =>
    inversion H; subst; clear H
  | H : (_, _) = (_,_) |- _ =>
    inversion H; subst; clear H
  end.
Ltac logical_simplify := repeat logical_simplify_step.

Section LogicalSimplifyTests.

  (* simple test: only and *)
  Goal (forall P Q, P /\ Q -> P).
    intros; logical_simplify. assumption.
  Qed.

  (* don't destruct ors (to avoid case explosion) *)
  Goal (forall P Q, P \/ Q -> True).
    intros.
    (* we expect to NOT simplify this goal! *)
    Fail progress logical_simplify.
    tauto.
  Qed.

  (* nested exists + and *)
  Goal (forall T P (Q : T -> Prop), (exists x, P x /\ Q x) -> exists x, Q x).
    intros; logical_simplify. eexists. eassumption.
  Qed.

  (* nested tuples *)
  Goal (forall T (a0 a1 a2 a3 b0 b1 b2 b3 : T),
           (a0,a1,a2,a3) = (b0,b1,b2,b3) ->
           a2 = b2).
    intros; logical_simplify. reflexivity.
  Qed.

  (* nested tuples + Some *)
  Goal (forall T (a0 a1 a2 a3 b0 b1 b2 b3 : T),
           (a0,a1,Some a2,a3) = (b0,b1,Some b2,b3) ->
           a2 = b2).
    intros; logical_simplify. reflexivity.
  Qed.

  (* more complex expression *)
  Goal (forall T (a0 a1 a2 a3 b0 b1 b2 b3 : T),
           (exists x,
               Some (a0, a1) = Some (b0, x)
               /\ Some x = Some b3) ->
           a1 = b3).
    intros; logical_simplify. reflexivity.
  Qed.
End LogicalSimplifyTests.

(* Import for boolsimpl tactic *)
Require Coq.Bool.Bool.

(* Rewrite database for boolsimpl *)
Lemma negb_true : negb true = false. Proof. reflexivity. Qed.
Lemma negb_false : negb false = true. Proof. reflexivity. Qed.
Hint Rewrite Bool.andb_true_l Bool.andb_true_r Bool.andb_diag
     Bool.andb_false_l Bool.andb_false_r Bool.andb_negb_l Bool.andb_negb_r
     Bool.orb_true_l Bool.orb_true_r Bool.orb_diag Bool.orb_false_l
     Bool.orb_false_r Bool.orb_negb_l Bool.orb_negb_r
     Bool.xorb_true_l Bool.xorb_true_r Bool.xorb_nilpotent Bool.xorb_false_l
     Bool.xorb_false_r Bool.negb_involutive negb_true negb_false
     using solve [eauto] : boolsimpl.

(* simplify boolean expressions *)
Ltac boolsimpl := autorewrite with boolsimpl; cbn [negb andb orb xorb].

Section BoolSimplTests.
  Goal (forall b : bool, ((negb b && b) || (b && negb (xorb b b)))%bool = b).
  Proof. intros. boolsimpl. reflexivity. Qed.
End BoolSimplTests.

(* simplify boolean hypotheses *)
Ltac boolsimpl_hyps :=
  autorewrite with boolsimpl in *; cbn [negb andb orb xorb] in *;
  repeat lazymatch goal with
         | H : (_ || _)%bool = true |- _ => apply Bool.orb_true_iff in H; destruct H
         | H : (_ || _)%bool = false |- _ => apply Bool.orb_false_iff in H; destruct H
         | H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H; destruct H
         | H : (_ && _)%bool = false |- _ => apply Bool.andb_false_iff in H; destruct H
         | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
         | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
         end.

Section BoolSimplHypsTests.
  Goal (forall b : bool, (b || negb true)%bool = true -> b = true).
  Proof. intros. boolsimpl_hyps. assumption. Qed.

  Goal (forall b : bool, (b || (negb b && false))%bool = true -> b = true).
  Proof. intros. boolsimpl_hyps. assumption. Qed.
End BoolSimplHypsTests.
