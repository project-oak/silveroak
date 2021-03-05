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
Require Import Coq.Vectors.Vector.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadLaws.
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.
Require Import Cava.Lib.BitVectorOps.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.Combinators.
Import VectorNotations ListNotations.
Open Scope list_scope.

Existing Instance CombinationalSemantics.

Section MapT.
  Lemma mapT_vector_ident {A B n} (f : A -> ident B) (v : Vector.t A n) :
    unIdent (mapT_vector f v) = map (fun a => unIdent (f a)) v.
  Proof.
    induction v; intros; [ reflexivity | ].
    cbn. rewrite IHv. reflexivity.
  Qed.
  (* Alternate form of the above with the Traversable wrapper not simplified *)
  Lemma mapT_vident {A B n} (f : A -> ident B) (v : Vector.t A n) :
    unIdent (Traversable.mapT
               (Traversable:=Traversable_vector)
               f v) = map (fun a => unIdent (f a)) v.
  Proof. apply mapT_vector_ident. Qed.

  Lemma mapT_lident {A B} (f : A -> ident B) (l : list A) :
    unIdent (Traversable.mapT
               (Traversable:=List.Traversable_list)
               f l) = List.map (fun a => unIdent (f a)) l.
  Proof.
    simpl. induction l; [ reflexivity | ].
    simpl. rewrite IHl. reflexivity.
  Qed.
End MapT.

Instance MonadLaws_ident : MonadLaws Monad_ident.
Proof. econstructor; intros; exact eq_refl. Defined.

(* Automation to help simplify expressions using the identity monad *)
Create HintDb simpl_ident discriminated.
Hint Rewrite @mapT_vector_ident @mapT_vident @mapT_lident using solve [eauto] : simpl_ident.
Ltac simpl_ident :=
  repeat
    first [ progress autorewrite with simpl_ident
          | progress cbn [fst snd bind ret Monad_ident monad
                              unpackV packV constant
                              CombinationalSemantics unIdent] ].
