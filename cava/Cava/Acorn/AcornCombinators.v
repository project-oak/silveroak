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

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
Import VectorNotations.
Local Open Scope vector_scope.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Import MonadNotation.
Open Scope monad_scope.

Require Export Acorn.AcornSignal.
Require Export Acorn.AcornCavaClass.
From Cava Require Import VectorUtils.
From Cava Require Import Monad.MonadFacts.

Open Scope type_scope.

Section WithCava.
  Context {signal} {cava : Cava signal}.
  
  Definition fork2 {m} `{Monad m}  {A : SignalType}
                  (input : signal A) : m (signal A * signal A) :=
    ret (input, input).

  (*
  -------------------------------------------------------------------------------
  -- 4-Sided tile col combinators
  -------------------------------------------------------------------------------
  -- COL r, where r :: (a, vec b) -> (vec c, a)
  --            a
  --            ^
  --            |
  --          -----
  --         |     |
  --     b ->|  r  |-> c
  --         |     |
  --          -----
  --            ^
  --            |
  --            a
  --            ^
  --            |
  --          -----
  --         |     |
  --     b ->|  r  |-> c
  --         |     |
  --          -----
  --            ^
  --            |
  --            a
  --            ^
  --            |
  --          -----
  --         |     |
  --     b ->|  r  |-> c
  --         |     |
  --          -----
  --            ^
  --            |
  --            a
  -------------------------------------------------------------------------------
  *)

  (* colV is a col combinator that works over Vector.t of signals.
    The input tuple is split into separate arguments so Coq can recognize
    the decreasing vector element.
  *)
  Fixpoint colV' {m} `{Monad m} {A B C} {n : nat}
                (circuit : A * B -> m (C * A))
                (aIn: A) (bIn: Vector.t B n) :
                m (Vector.t C n * A) :=
    match bIn with
    | [] => ret ([], aIn)
    | x::xs => '(b0, aOut) <- circuit (aIn, x) ;;
              '(bRest, aFinal) <- colV' circuit aOut xs ;;
                ret (b0::bRest, aFinal)
    end.

  Definition colV {m} `{Monad m} {A B C} {n : nat}
                  (circuit : A * B -> m (C * A))
                  (inputs: A * Vector.t B n) :
                  m (Vector.t C n * A) :=
  colV' circuit (fst inputs) (snd inputs).

  Local Close Scope vector_scope.

  Local Open Scope list_scope.

  (* List Variant *)

  Fixpoint colL' {m} `{Monad m} {A B C}
                (circuit : A * B -> m (C * A))
                (aIn: A) (bIn: list B) :
                m (list C * A) :=
    match bIn with
    | [] => ret ([], aIn)
    | x::xs => '(b0, aOut) <- circuit (aIn, x) ;;
              '(bRest, aFinal) <- colL' circuit aOut xs ;;
                ret (b0::bRest, aFinal)
    end.

  Definition colL {m} `{Monad m} {A B C}
                  (circuit : A * B -> m (C * A))
                  (inputs: A * list B) :
                  m (list C * A) :=
  colL' circuit (fst inputs) (snd inputs).

  (* TODO(satnam): Lemma about col_cons *)

  Definition zipWith `{Monad m} {A B C : SignalType} {n : nat}
           (f : signal A * signal B -> m (signal C))
           (a : signal (Vec A n))
           (b : signal (Vec B n))
           : m (signal (Vec C n)) :=
    let a' := peel a in
    let b' := peel b in
    v <- mapT f (vcombine a' b') ;;
    ret (unpeel v).

  Local Open Scope list_scope.

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

  Lemma foldLM_fold_right {m} `{Monad m} {A B}
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

  Lemma foldLM_ident_fold_left {m} `{Monad m}
        {A B} (f : B -> A -> ident B) ls b :
    unIdent (foldLM f ls b) = List.fold_left (fun b a => unIdent (f b a)) ls b.
  Proof.
    revert b; induction ls; [ reflexivity | ].
    cbn [foldLM List.fold_left]. intros.
    cbn [bind ret Monad_ident].
    rewrite IHls. reflexivity.
  Qed.
End WithCava.
