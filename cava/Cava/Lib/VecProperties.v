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

Require Import Coq.NArith.NArith.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.Vector.
Require Import Cava.Util.Identity.
Require Coq.Vectors.Vector.
Require Cava.Lib.Vec.
Import Vector.VectorNotations.
Local Open Scope vector_scope.

Existing Instance CombinationalSemantics.

Local Ltac crush :=
  (* inline Vec definition *)
  lazymatch goal with
  | |- ?x = _ =>
    let f := app_head x in cbv [f]
  end;
  cbv [Monad.mcompose]; simpl_ident; eauto;
  try solve
      [ repeat first [ rewrite map_id_ext; intros; simpl_ident
                     | reflexivity ] ].

Lemma bitvec_literal_correct n (v : Vector.t bool n) :
  Vec.bitvec_literal v = v.
Proof. crush. Qed.
Hint Rewrite @bitvec_literal_correct using solve [eauto] : simpl_ident.

Lemma of_N_correct n (x : N) : Vec.of_N x = N2Bv_sized n x.
Proof. crush. Qed.
Hint Rewrite @of_N_correct using solve [eauto] : simpl_ident.

Hint Rewrite @bitvec_literal_correct using solve [eauto] : simpl_ident.
Lemma map_literal_correct {A B} n (f : A -> cava (combType B)) (v : Vector.t A n) :
  Vec.map_literal f v = Vector.map f v.
Proof. crush. Qed.
Hint Rewrite @map_literal_correct using solve [eauto] : simpl_ident.

Lemma unpackV2_correct {A n0 n1} (v : combType (Vec (Vec A n0) n1)) :
  Vec.unpackV2 v = v.
Proof. crush. Qed.
Hint Rewrite @unpackV2_correct using solve [eauto] : simpl_ident.

Lemma unpackV3_correct {A n0 n1 n2} (v : combType (Vec (Vec (Vec A n0) n1) n2)) :
  Vec.unpackV3 v = v.
Proof. crush. Qed.
Hint Rewrite @unpackV3_correct using solve [eauto] : simpl_ident.

Lemma unpackV4_correct {A n0 n1 n2 n3}
      (v : combType (Vec (Vec (Vec (Vec A n0) n1) n2) n3)) :
  Vec.unpackV4 v = v.
Proof. crush. Qed.
Hint Rewrite @unpackV4_correct using solve [eauto] : simpl_ident.

Lemma packV2_correct {A n0 n1} (v : combType (Vec (Vec A n0) n1)) :
  Vec.packV2 v = v.
Proof. crush. Qed.
Hint Rewrite @packV2_correct using solve [eauto] : simpl_ident.

Lemma packV3_correct {A n0 n1 n2} (v : combType (Vec (Vec (Vec A n0) n1) n2)) :
  Vec.packV3 v = v.
Proof. crush. Qed.
Hint Rewrite @packV3_correct using solve [eauto] : simpl_ident.

Lemma packV4_correct {A n0 n1 n2 n3}
      (v : combType (Vec (Vec (Vec (Vec A n0) n1) n2) n3)) :
  Vec.packV4 v = v.
Proof. crush. Qed.
Hint Rewrite @packV4_correct using solve [eauto] : simpl_ident.

Lemma nil_correct A :
  @Vec.nil _ _ A = [].
Proof. crush. Qed.
Hint Rewrite @nil_correct using solve [eauto] : simpl_ident.

Lemma cons_correct A n x (v : combType (Vec A n)) :
  Vec.cons x v = (x :: v).
Proof. crush. Qed.
Hint Rewrite @cons_correct using solve [eauto] : simpl_ident.

Lemma tl_correct A n (v : combType (Vec A (S n))) :
  Vec.tl v = Vector.tl v.
Proof. crush. Qed.
Hint Rewrite @tl_correct using solve [eauto] : simpl_ident.

Lemma hd_correct A n (v : combType (Vec A (S n))) :
  Vec.hd v = Vector.hd v.
Proof. crush. Qed.
Hint Rewrite @hd_correct using solve [eauto] : simpl_ident.

Lemma const_correct A (x : combType A) n :
  Vec.const x n = Vector.const x n.
Proof. crush. Qed.
Hint Rewrite @const_correct using solve [eauto] : simpl_ident.

Lemma rev_correct A n (v : combType (Vec A (S n))) :
  Vec.rev v = Vector.reverse v.
Proof. crush. Qed.
Hint Rewrite @rev_correct using solve [eauto] : simpl_ident.

Lemma last_correct A n (v : combType (Vec A (S n))) :
  Vec.last v = Vector.last v.
Proof. crush. Qed.
Hint Rewrite @last_correct using solve [eauto] : simpl_ident.

Lemma shiftin_correct A n x (v : combType (Vec A n)) :
  Vec.shiftin x v = (Vector.shiftin x v).
Proof. crush. Qed.
Hint Rewrite @shiftin_correct using solve [eauto] : simpl_ident.

Lemma shiftout_correct A n (v : combType (Vec A (S n))) :
  Vec.shiftout v = Vector.shiftout v.
Proof. crush. Qed.
Hint Rewrite @shiftout_correct using solve [eauto] : simpl_ident.

Lemma transpose_correct A n m (v : combType (Vec (Vec A n) m)) :
  Vec.transpose v = transpose v.
Proof. crush. Qed.
Hint Rewrite @transpose_correct using solve [eauto] : simpl_ident.

Lemma reshape_correct A n m (v : combType (Vec A (n * m))) :
  Vec.reshape v = reshape v.
Proof. crush. Qed.
Hint Rewrite @reshape_correct using solve [eauto] : simpl_ident.

Lemma flatten_correct A n m (v : combType (Vec (Vec A m) n)) :
  Vec.flatten v = flatten v.
Proof. crush. Qed.
Hint Rewrite @flatten_correct using solve [eauto] : simpl_ident.

Lemma resize_default_correct A n m (v : combType (Vec A n)) :
  Vec.resize_default m v = resize_default (defaultCombValue A) m v.
Proof. crush. Qed.
Hint Rewrite @resize_default_correct using solve [eauto] : simpl_ident.

Lemma fold_left_correct A B n f b v :
  @Vec.fold_left _ _ A B f n v b
  = Vector.fold_left (fun x y => f (x,y)) b v.
Proof.
  revert v b; induction n; intros;
    [ apply Vector.case0 with (v:=v); reflexivity | ].
  rewrite (Vector.eta v).
  cbn [Vec.fold_left Vector.fold_left].
  simpl_ident. autorewrite with vsimpl.
  rewrite IHn. reflexivity.
Qed.
Hint Rewrite @fold_left_correct using solve [eauto] : simpl_ident.

Lemma fold_left2_correct A B C n f c i :
  @Vec.fold_left2 _ _ A B C f n i c
  = Vector.fold_left2 (fun x y z => f (x,y,z)) c (fst i) (snd i).
Proof.
  destruct i as [va vb].
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
  @Vec.map _ _ A B n f v = Vector.map f v.
Proof. crush. Qed.
Hint Rewrite @map_correct using solve [eauto] : simpl_ident.

Lemma map2_correct A B C n f i :
  @Vec.map2 _ _ A B C n f i
  = Vector.map2 (fun x y => f (x,y)) (fst i) (snd i).
Proof.
  crush. rewrite map_vcombine_map2.
  reflexivity.
Qed.
Hint Rewrite @map2_correct using solve [eauto] : simpl_ident.

Lemma inv_correct n (v : Vector.t bool n) :
  Vec.inv v = Vector.map negb v.
Proof. crush. Qed.
Hint Rewrite @inv_correct using solve [eauto] : simpl_ident.

Lemma and_correct n (i : Vector.t bool n * Vector.t bool n) :
  Vec.and i = Vector.map2 andb (fst i) (snd i).
Proof. crush. Qed.
Hint Rewrite @and_correct using solve [eauto] : simpl_ident.

Lemma nand_correct n (i : Vector.t bool n * Vector.t bool n) :
  Vec.nand i = Vector.map2 nandb (fst i) (snd i).
Proof. crush. Qed.
Hint Rewrite @nand_correct using solve [eauto] : simpl_ident.

Lemma or_correct n (i : Vector.t bool n * Vector.t bool n) :
  Vec.or i = Vector.map2 orb (fst i) (snd i).
Proof. crush. Qed.
Hint Rewrite @or_correct using solve [eauto] : simpl_ident.

Lemma nor_correct n (i : Vector.t bool n * Vector.t bool n) :
  Vec.nor i = Vector.map2 norb (fst i) (snd i).
Proof. crush. Qed.
Hint Rewrite @nor_correct using solve [eauto] : simpl_ident.

Lemma xor_correct n (i : Vector.t bool n * Vector.t bool n) :
  Vec.xor i = Vector.map2 xorb (fst i) (snd i).
Proof. crush. Qed.
Hint Rewrite @xor_correct using solve [eauto] : simpl_ident.

Lemma xnor_correct n (i : Vector.t bool n * Vector.t bool n) :
  Vec.xnor i = Vector.map2 xnorb (fst i) (snd i).
Proof. crush. Qed.
Hint Rewrite @xnor_correct using solve [eauto] : simpl_ident.

Lemma xorcy_correct n (i : Vector.t bool n * Vector.t bool n) :
  Vec.xorcy i = Vector.map2 xorb (fst i) (snd i).
Proof. crush. Qed.
Hint Rewrite @xorcy_correct using solve [eauto] : simpl_ident.
