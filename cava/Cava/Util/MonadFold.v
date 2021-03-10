(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadLaws.
Import ListNotations MonadNotation.
Local Open Scope monad_scope.

(* A list-based left monadic-fold. *)
Fixpoint foldLM {m} `{Monad m} {A B : Type}
         (f : B -> A -> m B)
         (input : list A)
         (accum : B)
  : m B :=
  match input with
  | [] => ret accum
  | k::ks => st' <- f accum k  ;;
           foldLM f ks st'
  end.

Lemma foldLM_fold_right {m} {monad:Monad m} {A B}
      (bind_ext : forall {A B} x (f g : A -> m B),
          (forall y, f y = g y) -> bind x f = bind x g)
      (f : B -> A -> m B) (input : list A) (accum : B) :
  foldLM f input accum =
  List.fold_right
    (fun k continuation v => bind (f v k) continuation)
    ret input accum.
Proof.
  revert accum; induction input; intros; [ reflexivity | ].
  cbn [foldLM List.fold_right].
  eapply bind_ext; intros.
  rewrite IHinput. reflexivity.
Qed.

Lemma foldLM_of_ret_valid {m} `{Monad m} `{MonadLaws m} {A B}
      (validA : A -> Prop) (validB : B -> Prop)
      (f : B -> A -> m B) (g : B -> A -> B) input accum :
  (forall b a, validA a -> validB b -> f b a = ret (g b a)) ->
  (forall b a, validA a -> validB b -> validB (g b a)) ->
  validB accum -> Forall validA input ->
  foldLM f input accum = ret (fold_left g input accum).
Proof.
  intro Hfg; revert accum; induction input; intros; [ reflexivity | ].
  cbn [foldLM fold_left].
  match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
  rewrite Hfg, MonadLaws.bind_of_return; auto.
Qed.

Lemma foldLM_of_ret {m} `{Monad m} `{MonadLaws m} {A B}
      (f : B -> A -> m B) (g : B -> A -> B) input accum :
  (forall b a, f b a = ret (g b a)) ->
  foldLM f input accum = ret (fold_left g input accum).
Proof.
  intro Hfg; revert accum; induction input; intros; [ reflexivity | ].
  cbn [foldLM fold_left]. rewrite Hfg, MonadLaws.bind_of_return by auto.
  apply IHinput.
Qed.
