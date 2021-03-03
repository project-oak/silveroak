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

Require Import Cava.Cava.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Identity.
Require Coq.Vectors.Vector.
Require Cava.Lib.Vec.
Import Vector.VectorNotations.
Local Open Scope vector_scope.

Existing Instance CombinationalSemantics.

Local Ltac crush :=
  (* inline Vec definition *)
  lazymatch goal with
  | |- unIdent ?x = _ =>
    let f := app_head x in cbv [f]
  end;
  simpl_ident; eauto using map_id_ext.


Lemma bitvec_literal_correct n (v : Vector.t bool n) :
  unIdent (Vec.bitvec_literal v) = v.
Proof. crush. Qed.
Hint Rewrite @bitvec_literal_correct using solve [eauto] : simpl_ident.

Lemma nil_correct A :
  unIdent (@Vec.nil _ _ A) = [].
Proof. crush. Qed.
Hint Rewrite @nil_correct using solve [eauto] : simpl_ident.

Lemma cons_correct A n x (v : combType (Vec A n)) :
  unIdent (Vec.cons x v) = (x :: v).
Proof. crush. Qed.
Hint Rewrite @cons_correct using solve [eauto] : simpl_ident.

Lemma tl_correct A n (v : combType (Vec A (S n))) :
  unIdent (Vec.tl v) = Vector.tl v.
Proof. crush. Qed.
Hint Rewrite @tl_correct using solve [eauto] : simpl_ident.

Lemma hd_correct A n (v : combType (Vec A (S n))) :
  unIdent (Vec.hd v) = Vector.hd v.
Proof. crush. Qed.
Hint Rewrite @hd_correct using solve [eauto] : simpl_ident.

Lemma const_correct A (x : combType A) n :
  unIdent (Vec.const x n) = Vector.const x n.
Proof. crush. Qed.
Hint Rewrite @const_correct using solve [eauto] : simpl_ident.

Lemma rev_correct A n (v : combType (Vec A (S n))) :
  unIdent (Vec.rev v) = Vector.rev v.
Proof. crush. Qed.
Hint Rewrite @rev_correct using solve [eauto] : simpl_ident.

Lemma last_correct A n (v : combType (Vec A (S n))) :
  unIdent (Vec.last v) = Vector.last v.
Proof. crush. Qed.
Hint Rewrite @last_correct using solve [eauto] : simpl_ident.

Lemma shiftin_correct A n x (v : combType (Vec A n)) :
  unIdent (Vec.shiftin x v) = (Vector.shiftin x v).
Proof. crush. Qed.
Hint Rewrite @shiftin_correct using solve [eauto] : simpl_ident.

Lemma shiftout_correct A n (v : combType (Vec A (S n))) :
  unIdent (Vec.shiftout v) = Vector.shiftout v.
Proof. crush. Qed.
Hint Rewrite @shiftout_correct using solve [eauto] : simpl_ident.

Lemma transpose_correct A n m (v : combType (Vec (Vec A n) m)) :
  unIdent (Vec.transpose v) = transpose v.
Proof.
  crush. rewrite !Vector.map_id; reflexivity.
Qed.
Hint Rewrite @transpose_correct using solve [eauto] : simpl_ident.

Lemma fold_left_correct A B n f b v :
  unIdent (@Vec.fold_left _ _ A B f n v b)
  = Vector.fold_left (fun x y => unIdent (f (x,y))) b v.
Proof.
  revert v b; induction n; intros;
    [ apply Vector.case0 with (v:=v); reflexivity | ].
  rewrite (Vector.eta v).
  cbn [Vec.fold_left Vector.fold_left].
  simpl_ident. autorewrite with vsimpl.
  rewrite IHn. reflexivity.
Qed.
Hint Rewrite @fold_left_correct using solve [eauto] : simpl_ident.

Lemma fold_left2_correct A B C n f c va vb :
  unIdent (@Vec.fold_left2 _ _ A B C f n va vb c)
  = Vector.fold_left2 (fun x y z => unIdent (f (x,y,z))) c va vb.
Proof.
  revert va vb c; induction n; intros;
    [ apply Vector.case0 with (v:=va);
      apply Vector.case0 with (v:=vb);
      reflexivity | ].
  rewrite (Vector.eta va), (Vector.eta vb).
  cbn [Vec.fold_left2 Vector.fold_left2].
  simpl_ident. autorewrite with vsimpl.
  rewrite IHn. reflexivity.
Qed.
Hint Rewrite @fold_left2_correct using solve [eauto] : simpl_ident.

Lemma map_correct A B n f v :
  unIdent (@Vec.map _ _ A B n f v)
  = Vector.map (fun x => unIdent (f x)) v.
Proof. crush. Qed.
Hint Rewrite @map_correct using solve [eauto] : simpl_ident.

Lemma map2_correct A B C n f va vb :
  unIdent (@Vec.map2 _ _ A B C n f va vb)
  = Vector.map2 (fun x y => unIdent (f (x,y))) va vb.
Proof.
  crush. rewrite map_vcombine_map2.
  reflexivity.
Qed.
Hint Rewrite @map2_correct using solve [eauto] : simpl_ident.
