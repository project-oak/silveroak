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
Require Import Cava.Lib.Decoder.
Require Import Cava.CavaProperties.

Import Circuit.Notations.

(* follows from parametricity... *)
Lemma map2_assoc : forall A f n,
  (forall (a b c :A),
    f a (f b c) = f (f a b) c) ->
    forall a b c,
      Vector.map2 (n:=n) f a (Vector.map2 f b c)
      = Vector.map2 f (Vector.map2 f a b) c.
Proof.
  intros.
  induction n.
  { repeat rewrite map2_0. trivial. }
  { repeat rewrite map2_cons. simpl.
    repeat rewrite IHn.
    rewrite H.
    trivial. }
Qed.

Lemma vec_const_eq_correct' : forall n k v,
  VecConstEq.vecConstEq n k v = eqb (N2Bv_sized n (N.of_nat k), v).
Proof.
  intros.
  cbv [VecConstEq.vecConstEq eqb].
  simpl.
  repeat rewrite map2_correct.
  simpl.
  rewrite Vector.map_id.
  rewrite Vector.map2_swap.
  apply f_equal.
  apply Vector.map2_ext.
  intros.
  destruct a; destruct b; trivial.
Qed.

Lemma vec_const_eq_correct : forall n k v,
  VecConstEq.vecConstEq n k v = combType_eqb (t:=Vec Bit n) (N2Bv_sized n (N.of_nat k)) v.
Proof.
  intros.
  replace (N2Bv_sized n (N.of_nat k)) with (fst ((N2Bv_sized n (N.of_nat k)),v)).
  2:trivial.
  replace v with (snd ((N2Bv_sized n (N.of_nat k)),v)) at 3.
  2:trivial.
  rewrite <- @eqb_correct with (t:=Vec Bit n).
  apply vec_const_eq_correct'.
Qed.

Lemma In_destruct : forall n A (a h:A) (v : Vector.t A n),
  Vector.In a (h :: v) -> a = h \/ Vector.In a v.
Proof.
  intros.
  inversion H.
  { left. trivial. }
  { right.
    apply Eqdep.EqdepTheory.inj_pair2 in H3.
    destruct H3.
    assumption. }
Qed.

Lemma fold_mono : forall [A n] [a:A] [f unit decider],
  (forall a b, decider a b = true <-> a = b) ->
  (forall b, f unit b = b) ->
  (forall b, f b unit = b) ->
  (forall b, f b b = b) ->
  forall (vec:Vector.t A n),
  Vector.fold_left f a (Vector.map (fun v => if decider a v then a else unit) vec) = a.
Proof.
  intros A n a f unit decider dec_true right left neutral vec.
  induction vec; trivial.
  cbn.
  case_eq (decider a h); intros; [rewrite neutral| rewrite left]; apply IHvec.
Qed.

Lemma iffb : forall P Q, (P = true <-> Q) ->  P = false <-> (not Q).
Proof.
  split.
  { cbv. intros. apply H in H1. destruct P; easy. }
  { destruct P; trivial.
    intros.
    exfalso.
    apply H0.
    apply H.
    trivial. }
Qed.

Lemma fold_units : forall A n (a:A) f unit decider,
  (forall a b, decider a b = true <-> a = b) ->
  (forall b, f unit b = b) ->
  (forall b, f b unit = b) ->
  (forall b, f b b = b) ->
  forall (vec:Vector.t A n),
  Vector.In a vec ->
  Vector.fold_left f unit (Vector.map (fun v => if decider a v then a else unit) vec) = a.
Proof.
intros A n a f unit decider dec_correct left right neutral vec guard.
induction vec.
{ inversion guard. }
{ cbn. rewrite left.
  case_eq (decider a h); intros.
  { apply (@fold_mono A n a f unit decider dec_correct left right neutral).  }
  { assert (forall a b : A, decider a b = false <-> a <> b) as dec_rev_correct.
    { intros. apply iffb.  apply dec_correct. }
    rewrite dec_rev_correct in H.
    apply IHvec.
    apply In_destruct in guard.
    inversion guard.
    { exfalso. apply H. apply H0. }
    { apply H0. } } }
Qed.

Lemma fold_units' : forall A n (a:A) f unit decider,
  (forall a b, decider a b = true <-> a = b) ->
  (forall b, f unit b = b) ->
  (forall b, f b unit = b) ->
  (forall b, f b b = b) ->
  forall (vec : Vector.t A n),
  forall vec',
  vec' = Vector.map (fun v => if decider a v then a else unit) vec ->
  Vector.In a vec ->
  Vector.fold_left f unit vec' = a.
Proof. intros. rewrite H3. apply fold_units; assumption. Qed.


Theorem In_map :
forall A B (n : nat) (a : A) f (v : Vector.t B n),
(exists x, f x = a /\ Vector.In x v) ->  Vector.In a (Vector.map f v).
Proof.
  intros.
  destruct H.
  destruct H.
  induction v.
  { inversion H0. }
  { inversion H0.
    { cbn. rewrite <- H3. rewrite H. apply Vector.In_cons_hd. }
    { cbn.
      apply Vector.In_cons_tl.
      apply IHv.
      apply Eqdep.EqdepTheory.inj_pair2 in H4.
      rewrite <- H4. trivial. }}
Qed.

Theorem In_list:
  forall n len start : nat, Vector.In n (vseq start len) <-> List.In n (seq start len).
Proof.
  induction len.
  { compute. split; intros; inversion H. }
  { split.
    { intros. inversion H.
      { left. trivial. }
      { apply Eqdep.EqdepTheory.inj_pair2 in H3.
        subst.
        right.
        apply IHlen.
        rewrite Nat.add_comm in H2.
        assumption. }}
    { cbn [In seq].
      intros [Hl | Hr].
      { subst. apply Vector.In_cons_hd. }
      { simpl. apply Vector.In_cons_tl. apply IHlen.  rewrite Nat.add_comm. apply Hr. } } }
Qed.

Theorem In_seq:
  forall n start len : nat, Vector.In n (vseq start len) <-> start <= n < start + len.
Proof.
  intros.
  rewrite In_list.
  Search seq.
  apply in_seq.
Qed.

Theorem Bv_span :
forall (n : nat) (a : Vector.t bool n),
Vector.In a
  (Vector.map (fun k : nat => N2Bv_sized n (N.of_nat k)) (vseq 0 (2 ^ n))).
Proof.
  intros.
  apply In_map.
  induction a.
  { apply ex_intro with (x:=0).
    split; trivial.
    apply Vector.In_cons_hd. }
  { inversion IHa.
    destruct h.
    { apply ex_intro with (x:=S(2*x)).
      split; destruct H.
      { rewrite Nat2N.inj_succ_double.
        rewrite N2Bv_sized_succ_double.
        rewrite H.
        trivial. }
      { apply In_seq. apply In_seq in H0. cbn in H0. cbn.
        lia. } } 
    { apply ex_intro with (x:=2*x).
      split; destruct H.
      { rewrite Nat2N.inj_double.
        rewrite N2Bv_sized_double.
        rewrite H.
        trivial. }
      { apply In_seq. apply In_seq in H0. cbn in H0. cbn.
        lia. } } }
Qed.

Theorem enc_dev_inv (n:nat) input : simulate ((Comb (decoder (n:=n))) >==>
  (Comb (encoder (n:=n)))) input = input.
Proof.
  (* Rewrite to [encoder ( decoder ) = id] *)
  autorewrite with push_simulate.
  rewrite map_map.
  apply List.map_id_ext.
  clear input.
  intros.

  cbv [decoder encoder Basics.compose].
  repeat rewrite map_literal_correct.
  repeat rewrite Vector.map_map.
  simpl.
  rewrite map2_correct.
  simpl.
  rewrite map2_map.
  rewrite map2_drop_same.
  rewrite @tree_equiv with (t:=Vec Bit n) (id:=Vector.const false n).
  2 :{ intros.
       rewrite map2_correct.
       simpl.
       rewrite map2_const.
       simpl.
       rewrite Vector.map_id.
       trivial. }
  2 :{ intros.
       rewrite map2_correct.
       simpl.
       rewrite map2_swap.
       rewrite map2_const.
       simpl.
       rewrite Vector.map_ext with (g:= id).
       { apply Vector.map_id. }
       { intros. apply orb_comm. } }
  3 :{ clear a.
       induction n.
       { compute. intros. inversion H. }
       { cbn. cbv ["<>"].
         intros.
         cbv ["<>"] in IHn.
         apply IHn.
         rewrite NPeano.Nat.add_assoc in H.
         rewrite Nat.add_0_r in H.
         apply Nat.eq_add_0 with (m:=2^n).
         assumption. } }
  2 :{ intros.
       repeat rewrite map2_correct.
       simpl.
       apply map2_assoc.
       intros.
       apply orb_assoc. }
  { simpl.
    cbv in a.
    rewrite Vector.map_ext with (g:= fun k => if combType_eqb (t:=Vec Bit n) (N2Bv_sized n (N.of_nat k)) a then N2Bv_sized  n (N.of_nat k) else Vector.const false n).
    2 :{ generalize (mux2_correct (t:=Vec Bit n)).
         intros.
         rewrite vec_const_eq_correct.
         simpl in H.
         rewrite H.
         rewrite Vector.map_id.
         trivial. }
    rewrite fold_left_ext with (g:=fun a0 b : Vector.t bool n => Vector.map2 (fun   x  y  => x || y)  a0  b ).
    2 :{ intros. rewrite map2_correct. apply map2_ext. auto. }
 replace (Vector.map
     (fun k : nat =>
      if combType_eqb (t:=Vec Bit n)(N2Bv_sized n (N.of_nat k)) a
      then N2Bv_sized n (N.of_nat k)
      else Vector.const false n) (vseq 0 (2 ^ n))) with (Vector.map
     (fun k =>
      if combType_eqb (t:=Vec Bit n) k a
      then k
      else Vector.const false n) (Vector.map (fun k => (N2Bv_sized n (N.of_nat k))) (vseq 0 (2 ^ n)))).
      2 :{ rewrite Vector.map_map. trivial. }
    apply fold_units' with (decider := (combType_eqb (t:=Vec Bit n)))
                           (vec:=(Vector.map (fun k : nat => N2Bv_sized n (N.of_nat k)) (vseq 0 (2 ^ n)))).
   { apply combType_eqb_true_iff. }
   { induction b; trivial.
     cbn. rewrite IHb; trivial.  }
   { induction b; trivial.
     cbn. rewrite IHb; trivial.
     destruct h; trivial.  }
   { induction b; trivial.
     cbn. rewrite IHb; trivial.
     destruct h; trivial.  }
   { apply Vector.map_ext. intros. cbn in a0.
    assert (forall a b, combType_eqb (t:=Vec Bit n) a b = false <-> a <> b) as combType_eqb_false_iff.
    { intros. apply iffb.  apply combType_eqb_true_iff. }
     case_eq (combType_eqb (t:=Vec Bit n) a0 a);
     case_eq (combType_eqb (t:=Vec Bit n) a a0);
     repeat rewrite combType_eqb_true_iff;
     repeat rewrite combType_eqb_false_iff; trivial; intros.
     { exfalso. apply H. auto. }
     { exfalso. apply H0. auto. } }
   { apply Bv_span. } }
Qed.


Definition N2hotv {n} k : Bvector n := Vector.reverse (unfold_ix tt (fun ix tt => (Nat.eqb k ix, tt))).

  (*
Theorem dec_correct : forall n k, k < 2^n -> decoder (N2Bv_sized n (N.of_nat k)) = N2hotv k.
Proof.
  intros.
  cbv [decoder].
  rewrite map_literal_correct.
  rewrite Vector.map_map.
  cbv [N2hotv].
  induction n; induction k; trivial.
  { inversion H. inversion H1. }

  rewrite map2_correct.

  rewrite map_literal_correct.
  induction a.
  {  trivial.  }
  { compute.



  cbv [decoder].
  cbv [encoder].


  intros.
  (* strategy: for the n -> S n case we (1) bash out the new k's (2) transport the old k s from the smaller n *)
  induction n.
  { inversion H.
    { trivial. }
    { inversion H1. }
  }
  { induction k.
    { Abort.

     *)
