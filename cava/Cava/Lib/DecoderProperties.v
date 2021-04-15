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

Lemma fold_mono {A B n} {a:A} {b: A-> B} {f unit decider}
  (dec_true : forall c d, decider c d = true <-> c = d)
  (right_id : forall c, f c unit = c)
  (neutral : forall c, f c c = c)
  (vec : Vector.t A n) :
  Vector.fold_left f (b a) (Vector.map (fun v => if decider a v then b v else unit) vec) = b a.
Proof.
  induction vec; [ trivial | ].
  cbn.
  case_eq (decider a h); intro H.
  { rewrite dec_true in H. subst.
    rewrite neutral.
    apply IHvec. }
  { remember (dec_contrapositive dec_true) as dec_false.
    rewrite dec_false in H. subst.
    rewrite right_id.
    apply IHvec. }
Qed.

Lemma fold_units {A B n} {a:A} {b: A -> B} f unit decider
  (dec_correct : forall c d, decider c d = true <-> c = d)
  (left_id : forall c, f unit c = c)
  (right_id : forall c, f c unit = c)
  (neutral : forall c, f c c = c)
  (vec : Vector.t A n)
  (guard : Vector.InV a vec) :
  Vector.fold_left f unit (Vector.map (fun v => if decider a v then b v else unit) vec) = b a.
Proof.
  induction vec; [ inversion guard | ]. cbn.
  rewrite left_id.
  case_eq (decider a h); intro a_is_h; [ | ].
  { apply dec_correct in a_is_h. destruct a_is_h.
    apply (@fold_mono A B n a b f unit decider dec_correct right_id neutral). }
  { remember (dec_contrapositive dec_correct) as dec_rev_correct.
    rewrite dec_rev_correct in a_is_h.
    apply IHvec.
    inversion guard; [ | ].
    { exfalso. apply a_is_h. assumption. }
    { assumption. }
  }
Qed.

Theorem fold_units' : forall A n (a:A) f unit decider,
  (forall c d, decider c d = true <-> c = d) ->
  (forall c, f unit c = c) ->
  (forall c, f c unit = c) ->
  (forall c, f c c = c) ->
  forall (vec : Vector.t A n) vec'
  (eq : vec' = Vector.map (fun v => if decider a v then a else unit) vec),
  Vector.InV a vec ->
  Vector.fold_left f unit vec' = a.
Proof. intros. rewrite eq. apply @fold_units with (b:= fun x => a); assumption. Qed.

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
    { induction c; trivial; [].
      cbn.
      rewrite IHc; trivial. }
    { induction c; trivial; [].
      cbn.
      rewrite IHc; trivial; [].
      destruct h; trivial. }
    { induction c; trivial; [].
      cbn.
      rewrite IHc; trivial; [].
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
        trivial; [ | ].
      { intros neq eq. exfalso. apply neq. easy. }
      { intros eq neq. exfalso. apply neq. easy. }
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

Definition N2hotv {n} k : Bvector n := Vector.map (fun m => if Nat.eqb k m then one else zero) (vseq 0 n).

Lemma map_id_guard : forall A f (g : A -> Prop) l
  (ext : forall (a : A),  g a -> f a = a)
  (guard : Forall g l),
  map f l = l.
Proof.
  intros.
  induction l.
  { trivial. }
  { simpl. rewrite ext.
    { rewrite IHl; trivial.
      inversion guard. trivial. }
    { inversion guard. trivial. }
  }
Qed.

Theorem map_ext_guard
  (A B : Type) (f g : A -> B)
  (P : A -> Prop)
  (ext : forall a : A, P a ->  f a = g a)
  (n : nat) (v : Vector.t A n)
  (Guard: forall a : A, InV a v -> P a)
  : Vector.map f v = Vector.map g v.
Proof.
  intros.
  induction v; [ trivial | ].
  cbn.
  rewrite IHv.
  { assert (f h = g h) as H.
    { apply ext. apply Guard. compute. left. reflexivity. }
    inversion H.
    reflexivity.
    }
  { intros. apply Guard.
    cbn. right.  assumption. }
Qed.

Lemma N_lt_step a : (N.of_nat a < N.of_nat (S a))%N.
Proof. rewrite Nat2N.inj_succ. apply N.lt_succ_diag_r. Qed.

Lemma N_lt_inj a b : a < b -> (N.of_nat a < N.of_nat b)%N.
Proof.
  rewrite <- N.compare_lt_iff.
  rewrite <- Nat.compare_lt_iff.
  rewrite Nat2N.inj_compare.
  trivial.
Qed.

Theorem dec_enc_inv (n:nat) (k : nat): k < 2^n ->
  @decoder combType Combinational.CombinationalSemantics n (encoder (N2hotv k)) = N2hotv k.
Proof.
  intro guard.
  cbv [decoder encoder].
  simpl_ident.
  autorewrite with vsimpl.
  cbv [combType].
  rewrite @tree_equiv with (t:=Vec Bit (n)) (id := Vector.const false (n));
   [ | | | | ].
  2:{ intros. simpl_ident. clear. induction n.
      { autorewrite with vsimpl. apply Vector.case0. trivial. }
      { rewrite const_cons. rewrite map2_cons. simpl. rewrite IHn.
        rewrite Vector.eta. trivial. }
  }
  2:{ intros. simpl_ident. clear. induction n.
      { autorewrite with vsimpl. apply Vector.case0. trivial. }
      { rewrite const_cons. rewrite map2_cons. simpl. rewrite IHn.
        rewrite orb_false_r.
        rewrite Vector.eta. trivial. }
  }
  2:{ intros. simpl_ident. apply map2_assoc.
      intros. apply orb_assoc. }
  2:{ clear. induction n.
      { easy. }
      { simpl. remember (2^n) as x. lia. }
  }
  { cbv [N2hotv].
    apply map_ext_guard with (P := fun i => i < 2^n );
      [ | intros a H; apply InV_seq in H; lia ].
    intros a.
    cbv [combType].
    rewrite Vector.map_map.
    rewrite map2_map.
    rewrite map2_drop_same.
    erewrite fold_left_ext;
      [ | intros ; simpl_ident; trivial ].
    rewrite Vector.map_ext with
      (f:= fun x =>
        mux2 (if (k =? x)%nat then one else zero)
          (defaultSignal,
           @Vec.bitvec_literal combType _ _ (N2Bv_sized n (N.of_nat x))))
      (g := fun x =>
        (if (k =? x)%nat
         then @Vec.bitvec_literal combType _ _ (N2Bv_sized n (N.of_nat x))
         else Vector.const false n)).
    2:{ intro a0. rewrite mux2_correct.
        case_eq(k=?a0)%nat; trivial. }
    rewrite fold_units; [ | | | | | ].
    { intros H. case_eq (k=?a)%nat.
      { intros H0.
        apply eq_sym in H0. apply EqNat.beq_nat_eq in H0. subst. simpl.
        simpl_ident.
        rewrite Vector.map2_map.
        rewrite map2_drop_same.
        rewrite Vector.map_ext with (g := fun x => true).
        2: { intros. cbv [xnorb]. rewrite xorb_nilpotent. trivial. }
        rewrite map_to_const.
        apply fold_left_andb_true. }
      { intros H0. apply EqNat.beq_nat_false in H0.
        rewrite eqb_correct.
        simpl.
        rewrite Vector.map_id.
        rewrite Vector.map_id.
        assert(
          Vector.eqb bool
            (fun x y : bool => Bool.eqb x y)
            (N2Bv_sized n (N.of_nat k))
            (N2Bv_sized n (N.of_nat a))
          = true
          -> False).
        { intros H1. apply H0. apply Vector.eqb_eq in H1.
          { apply f_equal with (f:=Bv2N) in H1. rewrite Bv2N_N2Bv_sized in H1.
            { rewrite Bv2N_N2Bv_sized in H1.
              { apply Nat2N.inj.  assumption. }
              { assert (N.of_nat 2 = 2%N) as H2; trivial.
                rewrite <- H2.
                rewrite Nat2N.inj_pow. 
                apply  N_lt_inj.
                assumption. }
            }
            { assert (N.of_nat 2 = 2%N) as H2; trivial.
              rewrite <- H2.
              rewrite Nat2N.inj_pow. 
              apply  N_lt_inj.
              assumption. }
          }
          { intros. split.
            { apply Bool.eqb_prop. }
            { intros. subst. destruct y; auto. }
          }
        }
        { case_eq(Vector.eqb bool
            (fun x y : bool => Bool.eqb x y)
            (N2Bv_sized n (N.of_nat k))
            (N2Bv_sized n (N.of_nat a))).
          { intros. exfalso. auto. }
          { trivial. }
        }
      }
    }
    { intros. split.
      { intros.
        apply EqNat.beq_nat_true.
        assumption. }
      { intros. subst. apply Nat.eqb_refl. }
    }
    { intros. rewrite Vector.map2_const. simpl. apply Vector.map_id. }
    { intros. rewrite Vector.map2_swap. rewrite Vector.map2_const.
      erewrite Vector.map_ext.
      2: { intros. apply orb_comm. }
      {  apply Vector.map_id. }
    }
    { intros. rewrite Vector.map2_drop_same. erewrite Vector.map_ext.
      2:{ intros. apply orb_diag. }
      { apply Vector.map_id. }
    }
    { apply InV_seq. lia. }
  }
Qed.
