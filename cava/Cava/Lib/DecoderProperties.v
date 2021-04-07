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

Require Import Coq.micromega.Lia.

Require Import Cava.Cava.
Require Import Cava.Lib.Decoder.

Require Import Cava.Lib.Lib.
Require Import Cava.Lib.CombinationalProperties.
Require Import Cava.Lib.CombinatorsProperties.
Require Import Cava.Lib.MultiplexersProperties.
Require Import Cava.Lib.CavaPreludeProperties.
Require Import Cava.Lib.VecProperties.

Require Import Cava.Util.Bool.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Vector.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.Tactics.
Require Import Cava.Semantics.Combinational.

Existing Instance CombinationalSemantics.

Import Circuit.Notations.

Lemma fold_mono {A n} {a:A} {f unit decider}
  (dec_true : forall a b, decider a b = true <-> a = b)
  (right_id : forall b, f b unit = b)
  (neutral : forall b, f b b = b)
  (vec : Vector.t A n) :
  Vector.fold_left f a (Vector.map (fun v => if decider a v then a else unit) vec) = a.
Proof.
  induction vec; [ trivial | ].
  cbn.
  case_eq (decider a h);
    intros;
    [rewrite neutral | rewrite right_id];
    apply IHvec.
Qed.

Lemma fold_units {A n} {a:A} {f unit decider}
  (dec_correct : forall a b, decider a b = true <-> a = b)
  (left_id : forall b, f unit b = b)
  (right_id : forall b, f b unit = b)
  (neutral : forall b, f b b = b)
  (vec : Vector.t A n)
  (guard : Vector.InV a vec) :
  Vector.fold_left f unit (Vector.map (fun v => if decider a v then a else unit) vec) = a.
Proof.
  induction vec; [ inversion guard | ]. cbn.
  rewrite left_id.
  case_eq (decider a h); intro a_is_h; [ | ].
  { apply (@fold_mono A n a f unit decider dec_correct right_id neutral). }
  { assert (forall a b : A, decider a b = false <-> a <> b) as dec_rev_correct.
    { intros. apply iffb. apply dec_correct. }
    rewrite dec_rev_correct in a_is_h.
    apply IHvec.
    inversion guard; [ | ].
    { exfalso. apply a_is_h. assumption. }
    { assumption. }
  }
Qed.

Theorem fold_units' : forall A n (a:A) f unit decider,
  (forall a b, decider a b = true <-> a = b) ->
  (forall b, f unit b = b) ->
  (forall b, f b unit = b) ->
  (forall b, f b b = b) ->
  forall (vec : Vector.t A n) vec'
  (eq : vec' = Vector.map (fun v => if decider a v then a else unit) vec),
  Vector.InV a vec ->
  Vector.fold_left f unit vec' = a.
Proof. intros. rewrite eq. apply fold_units; assumption. Qed.

Theorem enc_dev_inv (n:nat) input : simulate ((Comb (decoder (n:=n))) >==>
  (Comb (encoder (n:=n)))) input = input.
Proof.
  (* Rewrite to [encoder ( decoder ) = id] *)
  autorewrite with push_simulate.
  rewrite map_map.
  apply List.map_id_ext.
  clear input. intros.

  cbv [decoder encoder]. simpl_ident.
  repeat rewrite Vector.map_map.
  rewrite map2_map.
  rewrite map2_drop_same.
  rewrite @tree_equiv with (t:=Vec Bit n) (id:=Vector.const false n); [ | | | | ].
  (* Main branch *)
  { cbv in a.
    rewrite Vector.map_ext with
      (g := fun k =>
              if combType_eqb (t:=Vec Bit n) (N2Bv_sized n (N.of_nat k)) a
                 then N2Bv_sized n (N.of_nat k)
                 else Vector.const false n).
    2 :{ intros a0. simpl_ident.
         replace (N2Bv_sized n (N.of_nat a0)) with
                 (fst ((N2Bv_sized n (N.of_nat a0)),a)); trivial.
         rewrite <- @eqb_correct with (t:=Vec Bit n). simpl.
         rewrite map2_correct. rewrite map2_correct. rewrite map2_swap. cbn.
         unfold xnorb.
         replace ((Vector.map2 (fun b a1 : bool => negb (xorb a1 b))
                               (N2Bv_sized n (N.of_nat a0)) a)) with
                 ((Vector.map2 (fun a1 b : bool => negb (xorb a1 b))
                               (N2Bv_sized n (N.of_nat a0)) a)) ; [ trivial | ].
         apply map2_ext.
         intros. rewrite xorb_comm. trivial. }
    rewrite fold_left_ext with
      (g := fun a b : Vector.t bool n =>
              Vector.map2 (fun x y => x || y) a b).
    2 :{ intros. simpl_ident.
         apply map2_ext. trivial. }
    replace (Vector.map
              (fun k : nat =>
                if combType_eqb (t := Vec Bit n) (N2Bv_sized n (N.of_nat k)) a
                  then N2Bv_sized n (N.of_nat k)
                  else Vector.const false n) (vseq 0 (2 ^ n)))
      with
           (Vector.map
             (fun k =>
               if combType_eqb (t:=Vec Bit n) k a
                 then k
                 else Vector.const false n)
             (Vector.map
               (fun k => (N2Bv_sized n (N.of_nat k)))
               (vseq 0 (2 ^ n)))); [ | ].
    2 :{ rewrite Vector.map_map. trivial. }
    apply fold_units' with
      (decider := combType_eqb (t := Vec Bit n))
      (vec := Vector.map
                (fun k => N2Bv_sized n (N.of_nat k))
                (vseq 0 (2 ^ n))) ; [ | | | | | ].
    { apply combType_eqb_true_iff. }
    { induction b; trivial; [].
      cbn.
      rewrite IHb; trivial. }
    { induction b; trivial; [].
      cbn.
      rewrite IHb; trivial; [].
      destruct h; trivial. }
    { induction b; trivial; [].
      cbn.
      rewrite IHb; trivial; [].
      destruct h; trivial. }
    { apply Vector.map_ext.
      intros a0. cbn in a0.
      assert
        (forall a b, combType_eqb (t:=Vec Bit n) a b = false <-> a <> b)
        as combType_eqb_false_iff.
      { intros. apply iffb. apply combType_eqb_true_iff. }
      case_eq (combType_eqb (t:=Vec Bit n) a0 a);
        case_eq (combType_eqb (t:=Vec Bit n) a a0);
        repeat rewrite combType_eqb_true_iff;
        repeat rewrite combType_eqb_false_iff;
        trivial; intros; [ | ].
      { exfalso. apply H. easy. }
      { exfalso. apply H0. easy. }
    }
    { apply Bv_span. }
  }

  (* side conditions *)
  { intros. simpl_ident.
    rewrite map2_const.
    rewrite Vector.map_id. trivial. }
  { intros. simpl_ident.
    rewrite map2_swap.
    rewrite map2_const.
    simpl.
    rewrite Vector.map_ext with (g := id); [ | ].
    { apply Vector.map_id. }
    { intros. apply orb_comm. }
  }
  { intros. simpl_ident.
    apply map2_assoc.
    intros. apply orb_assoc. }
  { clear a. induction n; [ easy | ]. cbn.
    remember (2^n) as x.
    lia. }
Qed.
