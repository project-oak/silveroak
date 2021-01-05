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

(* Bit-vector arithmetic operations for Cava. *)


Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bvector.
Require Import Coq.NArith.Ndigits.
Require Import Coq.NArith.Nnat.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Coq.Strings.HexString.

Require Import Cava.NatUtils.
Require Import Cava.VectorUtils.

Import ListNotations.

Local Open Scope list_scope.

(* List and vector functions for conversion between nats and bit-vectors *)

Lemma lt_wf : well_founded lt.
Proof.
  apply well_founded_lt_compat with (f := id).
  tauto.
Defined.

Definition low_bit (n:nat) : bool := testbit n 0.

Definition fold_shift_nat {A} (base: A) (combine: nat -> bool -> A -> A) : nat -> A.
  refine (Fix lt_wf (fun _ => A)
              (fun (n:nat) f =>
                 if le_lt_dec n 0
                 then base
                 else combine (div2 n) (low_bit n) (f (div2 n) (PeanoNat.Nat.lt_div2 _ _)))).
  exact l.
Defined.

Fixpoint list_bits_to_nat' (bits : list bool) : nat :=
  match bits with
  | [] =>  0
  | b::bs => (shiftl (Nat.b2n b) (length bs)) + (list_bits_to_nat' bs)
  end.

Definition nat_to_list_bits' (n : nat) : list bool :=
  fold_shift_nat [] (fun x b l => l++[b]) n.

Definition nat_to_list_bits (n : N) : list bool :=
  to_list (N2Bv n).

Definition nat_to_list_bits_sized (size : nat) (n : N) : list bool :=
  to_list (N2Bv_sized size n).

Definition list_bits_to_nat (bv : list bool) : N :=
  Bv2N (of_list bv).

Example b2n_empty : list_bits_to_nat [] = 0%N.
Proof. reflexivity. Qed.

Example b2n_0 : list_bits_to_nat [false] = 0%N.
Proof. reflexivity. Qed.

Example b2n_1 : list_bits_to_nat [true] = 1%N.
Proof. reflexivity. Qed.

Example b2n_10 : list_bits_to_nat [false; true] = 2%N.
Proof. reflexivity. Qed.

Example b2n_01 : list_bits_to_nat [true; false] = 1%N.
Proof. reflexivity. Qed.

Example b2n_11 : list_bits_to_nat [true; true] = 3%N.
Proof. reflexivity. Qed.

Example n2b_0_1 : nat_to_list_bits 0 = [].
Proof. reflexivity. Qed.

Example n2b_1_1 : nat_to_list_bits 1 = [true].
Proof. reflexivity. Qed.

Example n2b_2_2 : nat_to_list_bits 2 = [false; true].
Proof. reflexivity. Qed.

Example n2b_2_3 : nat_to_list_bits 3 = [true; true].
Proof. reflexivity. Qed.

Lemma nat_of_list_bits_sized: forall (size :  nat) (v : N), size = N.size_nat v ->
      nat_to_list_bits_sized size v = nat_to_list_bits v.
Proof.
  intros.
  induction v.
  - unfold nat_to_list_bits. unfold nat_to_list_bits_sized.
    cbn [N2Bv_sized].
    rewrite H.  simpl. reflexivity.
  - rewrite H.
    unfold nat_to_list_bits_sized.
    rewrite N2Bv_sized_Nsize.
    unfold nat_to_list_bits.
    reflexivity.
Qed.

(* The following proof is from Steve Zdancewic. *)
Lemma bits_to_nat_app : forall u l, list_bits_to_nat' (u ++ l) = (list_bits_to_nat' u) * (shiftl 1 (length l)) + (list_bits_to_nat' l).
Proof.
  induction u; intros; simpl.
  - reflexivity.
  - rewrite IHu.
    rewrite Nat.mul_add_distr_r.
    destruct a.
    rewrite app_length.
    rewrite <- Nat.shiftl_shiftl.
    repeat rewrite Nat.shiftl_1_l.
    rewrite Nat.shiftl_mul_pow2.
    rewrite plus_assoc.
    reflexivity.
    repeat rewrite Nat.shiftl_0_l.
    simpl. reflexivity.
Qed.

Lemma nat_to_bits'_list_correct : forall n, list_bits_to_nat' (nat_to_list_bits' n) = n.
Proof.
  induction n using lt_wf_ind.
  unfold nat_to_list_bits'.
  unfold fold_shift_nat. rewrite Fix_eq.
  - destruct (le_lt_dec n 0).
    + assert (n = 0). lia. subst. simpl. reflexivity.
    + rewrite bits_to_nat_app.
      unfold nat_to_list_bits' in H.
      unfold fold_shift_nat in H.
      rewrite (H (div2 n)).
      unfold low_bit.
      simpl. replace (double 1) with 2 by auto.
      replace (Nat.b2n (odd n) + 0) with (Nat.b2n (odd n)) by lia.
      replace (div2 n * 2) with (2 * div2 n) by lia.
      rewrite Nat.div2_odd. reflexivity.
      apply Nat.lt_div2. assumption.
  - intros.
    destruct (le_lt_dec x 0).
    + reflexivity.
    + rewrite H0. reflexivity.
Qed.

(******************************************************************************)
(* Prove that an unsigned bit-vector b::bs represents the same number         *)
(* as b + 2 * bs i.e. the low bit represented as a number plus 2 times the    *)
(* the rest of the bit-vector.                                                *)
(******************************************************************************)

Local Open Scope N_scope.

Lemma list_bits_to_nat_cons b bs :
  list_bits_to_nat (b :: bs) = N.b2n b + 2 * list_bits_to_nat bs.
Proof.
  (* Unfold the definition of list_bits_to_nat to get an expression
     in terms of BvN. *)
  unfold list_bits_to_nat.
  (* We now have:
       Bv2N (of_list (b :: bs)) = N.b2n b + 2 * Bv2N (of_list bs)
     Bv2N (of_list (b :: bs)) converts the list b::bs to a Bvector (Vector bool)
     which is converted by Bv2N to the natural type N. Unfold one application
     of the of_list function which converts a list to a vector. *)
  cbn [of_list Bv2N].
  (* We now have:
       (if b
         then N.succ_double (Bv2N (of_list bs))
         else N.double (Bv2N (of_list bs))) = N.b2n b + 2 * Bv2N (of_list bs)
     Let's take apart the if statement by destructing on its conditional
     value b. In each branch let's also unfold the N.b2n function that converts
     a bool value to a value of the natural type N. *)
  destruct b; unfold N.b2n.
  (* We now have:
     1/2
     N.succ_double (Bv2N (of_list bs)) = 1 + 2 * Bv2N (of_list bs)
     2/2
    N.double (Bv2N (of_list bs)) = 0 + 2 * Bv2N (of_list bs) *)
  - (* 1/2: Let's use the following lemma:
       Lemma succ_double_spec n : succ_double n = 2 * n + 1.
       This says that succ_dobule of n is the same as doubling n and adding 1.
       This gives:
         2 * Bv2N (of_list bs) + 1 = 1 + 2 * Bv2N (of_list bs)
       which can be proved bu the lia hammer. *)
    rewrite N.succ_double_spec. lia.
  - (* 2/2: Let's use the lemma:
       Lemma double_spec n : double n = 2 * n.
       This says the double n is the same as 2 * b.
       This gives:
         2 * Bv2N (of_list bs) = 0 + 2 * Bv2N (of_list bs)
       which can be solved by the lia hammer. *)
    rewrite N.double_spec. lia.
Qed.

Local Close Scope N_scope.

(******************************************************************************)
(* Functions useful for Vector operations                                     *)
(******************************************************************************)

Definition bitvec_to_nat {n : nat} (bits : Bvector n) : nat :=
  N.to_nat (Bv2N n bits).

Definition bv3_0 : Bvector 3 := [false; false; false]%vector.
Example bv3_0_ex : bitvec_to_nat bv3_0 = 0.
Proof. reflexivity. Qed.

Definition bv1 : Bvector 1 := [true]%vector.
Example bv1_ex : bitvec_to_nat bv1 = 1.
Proof. reflexivity. Qed.

Definition bv3_1 : Bvector 3 := [true; false; false]%vector.
Example bv3_1_ex : bitvec_to_nat bv3_1 = 1.
Proof. reflexivity. Qed.

Definition bv3_2 : Bvector 3 := [false; true; false]%vector.
Example bv3_2_ex : bitvec_to_nat bv3_2 = 2.
Proof. reflexivity. Qed.

Definition nat_to_bitvec (v : nat) : Bvector (N.size_nat (N.of_nat v)) :=
  N2Bv (N.of_nat v).

Definition nat_to_bitvec_sized (n : nat) (v : nat) : Bvector n :=
  N2Bv_sized n (N.of_nat v).

Example bv3_0_cancellev : nat_to_bitvec_sized 3 0 = bv3_0.
Proof. reflexivity. Qed.

Example bv3_1_cancellev : nat_to_bitvec_sized 3 1 = bv3_1.
Proof. reflexivity. Qed.

Example bv3_2_cancellev : nat_to_bitvec_sized 3 2 = bv3_2.
Proof. reflexivity. Qed.

(* Vector version of list seq *)
Fixpoint vec_seq (a b : nat) : Vector.t nat b :=
  match b with
  | 0 => Vector.nil nat
  | S b' => Vector.cons nat a b' (vec_seq (a + 1) b')
  end.

(* Vector version of replicate *)
Fixpoint replicate_vec {A : Type} (n : nat) (v : A) : Vector.t A n :=
  match n with
  | 0    => Vector.nil A
  | S n' => Vector.cons A v n' (replicate_vec n' v)
  end.

Lemma bits_of_nat_sized: forall n bv, nat_to_bitvec_sized n (bitvec_to_nat bv) = bv.
Proof.
  intros.
  unfold nat_to_bitvec_sized.
  unfold bitvec_to_nat.
  rewrite N2Nat.id.
  rewrite N2Bv_sized_Bv2N.
  reflexivity.
Qed.

Lemma nat_of_bits: forall v, bitvec_to_nat (nat_to_bitvec v) = v.
Proof.
  intros.
  unfold nat_to_bitvec.
  unfold bitvec_to_nat.
  rewrite Bv2N_N2Bv.
  rewrite Nat2N.id.
  reflexivity.
Qed.

Lemma nat_of_bits_sized: forall (v : nat),
      bitvec_to_nat (nat_to_bitvec_sized (N.size_nat (N.of_nat v)) v) = v.
Proof.
  intros.
  unfold nat_to_bitvec_sized.
  unfold bitvec_to_nat.
  rewrite N2Bv_sized_Nsize.
  rewrite Bv2N_N2Bv.
  rewrite Nat2N.id.
  reflexivity.
Qed.

Lemma Pos_size_nat_nonzero (p : positive) : 0 < Pos.size_nat p.
Proof. destruct p; cbn; lia. Qed.

Lemma N_size_nat_le0 (x : N) : N.size_nat x = 0 -> x = 0%N.
Proof.
  destruct x as [|p]; [ reflexivity | ].
  pose proof (Pos_size_nat_nonzero p).
  cbn [N.size_nat]. lia.
Qed.

Lemma P2Bv_nonzero (n : nat) (p : positive) :
  (Pos.size_nat p <= n) ->
  P2Bv_sized n p <> Bvector.Bvect_false n.
Proof.
  pose proof (Pos_size_nat_nonzero p).
  revert dependent p; induction n; destruct p; intros;
    cbn in *; try congruence; try lia; [ ].
  let Heq := fresh in
  intro Heq; apply cons_inj in Heq; destruct Heq.
  eapply IHn; eauto using Pos_size_nat_nonzero; [ ].
  lia.
Qed.

Lemma P2Bv_sized_eq_iff (n : nat) (x y : positive) :
  (Pos.size_nat x <= n) ->
  (Pos.size_nat y <= n) ->
  (P2Bv_sized n x = P2Bv_sized n y) <-> x = y.
Proof.
  revert x y; induction n; intros.
  { pose proof (Pos_size_nat_nonzero x).
    pose proof (Pos_size_nat_nonzero y).
    split; [ intros; lia | reflexivity]. }
  { split; try congruence; [ ].
    cbn [P2Bv_sized].
    destruct x, y; try congruence; [ | | | ].
    all:cbn [Pos.size_nat] in *.
    all:let H := fresh in
        intro H; apply cons_inj in H; destruct H.
    all:lazymatch goal with
        | H : P2Bv_sized _ _ = P2Bv_sized _ _ |- _ =>
          rewrite IHn in H by lia; subst
        | H : P2Bv_sized _ _ = Bvector.Bvect_false _ |- _ =>
          apply P2Bv_nonzero in H; [ | lia ]
        | H : Bvector.Bvect_false _ = P2Bv_sized _ _ |- _ =>
          symmetry in H; apply P2Bv_nonzero in H; [ | lia ]
        end.
    all:tauto. }
Qed.

Lemma N2Bv_sized_eq_iff (n : nat) (x y : N) :
  (N.size_nat x <= n) ->
  (N.size_nat y <= n) ->
  (N2Bv_sized n x = N2Bv_sized n y) <-> x = y.
Proof.
  destruct x, y; cbn [N.size_nat N2Bv_sized]; intros; split; intros.
  all:try lazymatch goal with
          | H : P2Bv_sized _ _ = P2Bv_sized _ _ |- _ =>
            rewrite P2Bv_sized_eq_iff in H by lia; subst
          | H : P2Bv_sized _ _ = Bvector.Bvect_false _ |- _ =>
            apply P2Bv_nonzero in H; [ | lia ]
          | H : Bvector.Bvect_false _ = P2Bv_sized _ _ |- _ =>
            symmetry in H; apply P2Bv_nonzero in H; [ | lia ]
          end.
  all:(tauto || congruence).
Qed.

Lemma Bv2N_append {n m} (v1 : Bvector.Bvector n) (v2 : Bvector.Bvector m) :
  Bv2N (v1 ++ v2)%vector = (Bv2N v1 + N.shiftl (Bv2N v2) (N.of_nat n))%N.
Proof.
  revert v1 v2; induction n.
  { intros v1 ?; eapply case0 with (v:=v1).
    simpl. rewrite N.shiftl_0_r. reflexivity. }
  { intros v1 ?. rewrite (eta v1).
    rewrite <-append_comm_cons. cbn [Bv2N].
    rewrite IHn. rewrite !N.succ_double_add, !N.double_add.
    rewrite Nat2N.inj_succ, N.shiftl_succ_r.
    rewrite !N.succ_double_spec, !N.double_spec.
    repeat lazymatch goal with
           | |- context [N.double ?n] => rewrite (N.double_spec n)
           end.
    destruct (Vector.hd v1); lia. }
Qed.

Lemma Bv2N_Bvect_false n : Bv2N (Bvector.Bvect_false n) = 0%N.
Proof.
  induction n; [ reflexivity | ]. simpl. rewrite IHn. reflexivity.
Qed.

Lemma Bv2N_N2Bv_sized sz n :
  (n < 2 ^ N.of_nat sz)%N -> Bv2N (N2Bv_sized sz n) = n.
Proof.
  intros. pose proof (N.size_nat_le _ _ ltac:(eauto)).
  replace sz with (N.size_nat n + (sz - N.size_nat n)) by lia.
  rewrite N2Bv_N2Bv_sized_above. rewrite Bv2N_append, Bv2N_Bvect_false.
  rewrite N.shiftl_0_l, N.add_0_r. apply Bv2N_N2Bv.
Qed.

Lemma nat_to_bitvec_to_nat sz n :
  n < 2 ^ sz ->
  N.to_nat (Bv2N (nat_to_bitvec_sized sz n)) = n.
Proof.
  intros. cbv [nat_to_bitvec_sized].
  rewrite Bv2N_N2Bv_sized; [ solve [apply Nat2N.id] | ].
  change 2%N with (N.of_nat 2). rewrite Nat2N.inj_pow.
  lia.
Qed.

(******************************************************************************)
(* Functions useful for examples and tests                                    *)
(******************************************************************************)

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

Definition n2bool (n : N) : bool :=
  match n with
  | 0%N => false
  | _   => true
  end.

Definition fromVec := List.map Nat.b2n.
Definition toVec := List.map nat2bool.

Definition Bv2Hex {n} (x: Vector.t bool n) := HexString.of_N (Bv2N x).
Definition Hex2Bv {n} (s : String.string) := N2Bv_sized n (HexString.to_N s).

Definition byte_reverse {n} (x: Vector.t bool (n*8)) := flatten (reverse (reshape (m:=8) x)).

Definition bitvec_to_byte (v : Vector.t bool 8) : Byte.byte :=
  let '(b0,v) := Vector.uncons v in
  let '(b1,v) := Vector.uncons v in
  let '(b2,v) := Vector.uncons v in
  let '(b3,v) := Vector.uncons v in
  let '(b4,v) := Vector.uncons v in
  let '(b5,v) := Vector.uncons v in
  let '(b6,v) := Vector.uncons v in
  let '(b7,v) := Vector.uncons v in
  Byte.of_bits (b0,(b1,(b2,(b3,(b4,(b5,(b6,b7))))))).

Definition byte_to_bitvec (b : Byte.byte) : Vector.t bool 8 :=
  Ndigits.N2Bv_sized 8 (Byte.to_N b).
Definition bitvec_to_bytevec n (v : Vector.t bool (n * 8)) : Vector.t Byte.byte n :=
  Vector.map bitvec_to_byte (reshape v).
Definition bytevec_to_bitvec n (v : Vector.t Byte.byte n) : Vector.t bool (n * 8) :=
  flatten (Vector.map byte_to_bitvec v).

Definition bytevec_to_wordvec
           bytes_per_word n (v : Vector.t Byte.byte (n * bytes_per_word))
  : Vector.t (Vector.t Byte.byte bytes_per_word) n := reshape v.

Definition bitvec_to_wordvec
           bits_per_word n (v : Vector.t bool (n * bits_per_word))
  : Vector.t (Vector.t bool bits_per_word) n := reshape v.

Definition wordvec_to_bytevec
           bytes_per_word {n} (v : Vector.t (Vector.t Byte.byte bytes_per_word) n)
  : Vector.t Byte.byte (n * bytes_per_word) := flatten v.
Definition wordvec_to_bitvec
           bits_per_word {n} (v : Vector.t (Vector.t bool bits_per_word) n)
  : Vector.t bool (n * bits_per_word) := flatten v.

Lemma byte_to_bitvec_to_byte b :
  bitvec_to_byte (byte_to_bitvec b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma bitvec_to_byte_to_bitvec v :
  byte_to_bitvec (bitvec_to_byte v) = v.
Proof.
  cbv [bitvec_to_byte byte_to_bitvec].
  constant_vector_simpl v.
  autorewrite with vsimpl.
  match goal with
  | |- context [Byte.of_bits (?b0, (?b1, (?b2, (?b3, (?b4, (?b5, (?b6, ?b7)))))))] =>
    destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity
  end.
Qed.

Lemma bytevec_to_bitvec_to_bytevec n v :
  bitvec_to_bytevec n (bytevec_to_bitvec n v) = v.
Proof.
  cbv [bitvec_to_bytevec bytevec_to_bitvec].
  autorewrite with vsimpl. rewrite map_map.
  apply map_id_ext; intros.
  apply byte_to_bitvec_to_byte.
Qed.

Lemma bitvec_to_bytevec_to_bitvec n v :
  bytevec_to_bitvec n (bitvec_to_bytevec n v) = v.
Proof.
  cbv [bitvec_to_bytevec bytevec_to_bitvec].
  rewrite map_map, map_id_ext by (intros; apply bitvec_to_byte_to_bitvec).
  autorewrite with vsimpl; reflexivity.
Qed.

