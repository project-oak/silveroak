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

Require Import Coq.Vectors.Vector.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.Vector.
Import VectorNotations.

Existing Instance CombinationalSemantics.

(* Equality of combinational signals is decidable *)
Section DecidableEquality.
  Fixpoint combType_eqb {t} : combType t -> combType t -> bool :=
    match t as t0 return combType t0 -> combType t0 -> bool with
    | Void => fun _ _ => true
    | Bit => fun x y => Bool.eqb x y
    | Vec A n => fun x y => Vector.eqb _ combType_eqb x y
    | ExternalType s => fun x y => true
    end.

  Lemma combType_eqb_true_iff {t} (x y : combType t) :
    combType_eqb x y = true <-> x = y.
  Proof.
    revert x y; induction t; intros;
      repeat match goal with
             | _ => progress cbn [combType_eqb combType Bool.eqb fst snd] in *
             | x : unit |- _ => destruct x
             | x : bool |- _ => destruct x
             | x : _ * _ |- _ => destruct x
             | _ => tauto
             | _ => solve [eauto using VectorEq.eqb_eq]
             | |- _ <-> _ => split; congruence
             end.
  Qed.
End DecidableEquality.

Section Indexing.
  Lemma indexAt2_correct {t} (i0 i1 : combType t) (sel : combType Bit) :
    indexAt [i0; i1]%vector [sel]%vector = if sel then i1 else i0.
  Proof. destruct sel; reflexivity. Qed.
  Hint Rewrite @indexAt2_correct using solve [eauto] : simpl_ident.

  Lemma indexConst_eq {A sz} (v : combType (Vec A sz)) (n : nat) :
    indexConst v n = nth_default (defaultCombSignal _) n v.
  Proof. reflexivity. Qed.
  Hint Rewrite @indexConst_eq using solve [eauto] : simpl_ident.
End Indexing.
