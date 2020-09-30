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

(* The instantiate_lhs_app_by_reflexivity tactic works on goals of the form:

   f x = g

   ... where f is an evar. It works by patterning out any occurences of [x] in
   the term [g] (i.e. changing [g] into an application of some function to [x])
   and then instantiating [f] with the resulting function. *)
Ltac instantiate_lhs_app_by_reflexivity :=
  lazymatch goal with
  | |- ?g ?x = ?rhs =>
    is_evar g;
    lazymatch rhs with
    | context [x] =>
      match (eval pattern x in rhs) with
      | ?f _ =>
        let H := fresh in
        assert (forall y, f y = g y) as H;
        [ intros; reflexivity | solve [apply H] ]
      end
    | _ =>
      (* x does not appear on RHS, so ignore the argument *)
      assert (g = (fun _ => rhs)); reflexivity
    end
  | |- ?G => fail "Expected goal of form [?g ?x = ?rhs] (where g must be an evar), got" G
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
End InstantiateAppByReflexivityTests.
