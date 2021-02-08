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

Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Structures.Monad.

Require Import Cava.Acorn.Acorn.

Local Open Scope monad_scope.

(* This instance allows the use of functional extensionality on identity-monad
   bind *)
Lemma ident_bind_Proper_ext : forall A B (x : ident A) (f : A -> ident B)
                                                       (g : A -> ident B),
  (forall a, f a = g a) -> (x >>= f) = (x >>= g).
Proof.
  intros. (* Introduce quantified variables.
    t: Type
    u: Type
    x: ident t
    f, g: t -> ident u
    H: forall a : t, f a = g a
    ---------------------------
    ` x : _ <- x;; f x = ` x : _ <- x;; g x   *)
  simpl. (* Simplify to boil down to applications of unIdent
    f (unIdent x) = g (unIdent x) *)
  auto. (* auto can use H in our context to discharge the proof. *)
Qed.

(* Right identity monad law specialized to the identity monad:
  x >>= ret = x  *)
Lemma ident_bind_ret A (x : ident A) : x >>= ret = x.
Proof.
  (* Desugared:
       x : _ <- x;; ret x = x *)
  destruct x. (* Take apart on x
      x : _ <- {| unIdent := unIdent |};;
      ret x = {| unIdent := unIdent |} *)
  simpl. (* Perform unfolding simplifications:
    {| unIdent := unIdent |} = {| unIdent := unIdent |}   *)
  reflexivity.
Qed.

(* Recognize a bind of bind *)
Lemma ident_bind_lift_app {A B C} (f : A -> B) (g : B -> C) 
                          (x : ident A) :
  x >>= (fun y => ret (g (f y))) =
  x >>= (fun y => ret (f y)) >>= (fun y => ret (g y)).
Proof.
  destruct x. (* Take apart on x
    y : A <- {| unIdent := unIdent |};;
    ret (g (f y)) =
    (y : A <- {| unIdent := unIdent |};;
      ret (f y)
    ) ;;
    ret (g y)  *)
  reflexivity.
Qed.

Hint Rewrite @bind_of_return @bind_associativity
     using solve [typeclasses eauto] : monadlaws.

(* Prove that Monad_ident is an instance of MonadLaw.
   Should this really be in coq-ext-lib? *)
Instance MonadLaws_ident : MonadLaws Monad_ident.
Proof. constructor; intros; reflexivity. Qed.

(* Decompose a serial composition of circuits f and g into
   two separate semantic interpretations. *)
Lemma semantics_bind {A B} (f : ident A) (g : A -> ident B) :
  semantics (f >>= g) = semantics (g (semantics f)).
Proof.
  destruct f. (* Take apart on the circuit f.
    semantics (` x : _ <- {| unIdent := unIdent |};; g x) =
    semantics (g (semantics {| unIdent := unIdent |}))   *)
  reflexivity. (* Both sides boil down to computing x as the result of
                  circuit f which is passed as an argument to circuit g *)
Qed.

(* The semantic interpretation of the `return` of any value is
   just the same value. *)
Lemma semantics_ret {A} (x : A) : semantics (ret x) = x.
Proof. reflexivity. Qed.

