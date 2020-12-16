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

Require Import Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monad.
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Lib.BitVectorOps.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.CombinationalMonad.
Require Import Cava.Acorn.Combinators.

Existing Instance CombinationalSemantics.

(* Lemmas about combinators specialized to the identity monad *)
Section Combinators.
  Lemma zipWith_unIdent {A B C : SignalType} n f va vb :
    unIdent (@zipWith _ _ Monad_ident A B C n f va vb)
    = map2 (fun a b => unIdent (f (a,b))) va vb.
  Proof.
    cbv [zipWith Traversable.mapT Traversable_vector].
    cbn [peel unpeel CombinationalSemantics].
    revert va vb; induction n; intros; [ apply nil_eq | ].
    cbn [vcombine]. rewrite (eta va), (eta vb).
    autorewrite with push_vector_map vsimpl.
    rewrite <-IHn. reflexivity.
  Qed.
End Combinators.


Section Vectors.
  Lemma xorV_unIdent n ab :
    unIdent (@xorV _ _ Monad_ident n ab) = map2 xorb (fst ab) (snd ab).
  Proof.
    cbv [xorV Traversable.mapT Traversable_vector].
    cbn [peel unpeel CombinationalSemantics]. destruct ab as [a b].
    revert a b; induction n; intros; [ apply nil_eq | ].
    cbn [vcombine]. rewrite (eta a), (eta b).
    autorewrite with push_vector_map vsimpl.
    cbn [fst snd] in *.
    rewrite <-IHn. reflexivity.
  Qed.
End Vectors.

(* Automation to help simplify expressions using the identity monad *)
Create HintDb simpl_ident discriminated.
Hint Rewrite @zipWith_unIdent @xorV_unIdent
     using solve [eauto]: simpl_ident.
Ltac simpl_ident :=
  repeat
    first [ progress autorewrite with simpl_ident
          | erewrite map2_ext; [ | intros; progress simpl_ident;
                                   instantiate_app_by_reflexivity ]
          | erewrite map_ext; [ | intros; progress simpl_ident;
                                  instantiate_app_by_reflexivity ]
          | erewrite fold_left_ext; [ | intros; progress simpl_ident;
                                        instantiate_app_by_reflexivity ]
          | progress cbn [fst snd bind ret Monad_ident unIdent] ].
