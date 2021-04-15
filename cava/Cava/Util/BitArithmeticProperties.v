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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Vectors.Vector.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Vector.
Require Import Cava.Util.BitArithmetic.
Import ListNotations.
Local Open Scope N_scope.

(* Destructs into cases for all possible values of a constant-length bit
   vector *)
Ltac constant_bitvec_cases vec :=
  lazymatch type of vec with
  | Vector.t bool (S ?n) =>
      let v' := fresh "v" in
      rewrite (Vector.eta vec); set (v' := Vector.tl vec);
      cbv beta in v'; constant_bitvec_cases v';
      destruct (Vector.hd vec)
  | Vector.t bool 0 => eapply Vector.case0 with (v := vec)
  end.

Lemma to_list_bits_sized_size : forall (size :  nat) (v : N), size = N.size_nat v ->
      N.to_list_bits_sized size v = N.to_list_bits v.
Proof.
  intros.
  induction v.
  - unfold N.to_list_bits. unfold N.to_list_bits_sized.
    cbn [N2Bv_sized].
    rewrite H.  simpl. reflexivity.
  - rewrite H.
    unfold N.to_list_bits_sized.
    rewrite N2Bv_sized_Nsize.
    unfold N.to_list_bits.
    reflexivity.
Qed.

(******************************************************************************)
(* Prove that an unsigned bit-vector b::bs represents the same number         *)
(* as b + 2 * bs i.e. the low bit represented as a number plus 2 times the    *)
(* the rest of the bit-vector.                                                *)
(******************************************************************************)

Lemma N_of_list_bits_cons b bs :
  N.of_list_bits (b :: bs) = N.b2n b + 2 * N.of_list_bits bs.
Proof.
  (* Unfold the definition of list_bits_to_nat to get an expression
     in terms of BvN. *)
  unfold N.of_list_bits.
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


Lemma N_of_list_bits_zero n : N.of_list_bits (repeat false n) = 0%N.
Proof.
  induction n; [ reflexivity | ].
  cbn [repeat]; rewrite N_of_list_bits_cons, IHn.
  cbn [N.b2n]. lia.
Qed.

Lemma N_of_list_bits_nil : N.of_list_bits [] = 0%N.
Proof. reflexivity. Qed.

Lemma N_of_list_bits_app l1 l2 :
  N.of_list_bits (l1 ++ l2)
  = (N.of_list_bits l1 + 2 ^ (N.of_nat (length l1)) * N.of_list_bits l2)%N.
Proof.
  revert l2; induction l1; intros; cbn [app length].
  { destruct l2; [ reflexivity | ].
    change (2 ^ (N.of_nat 0))%N with 1%N.
    rewrite !N_of_list_bits_cons, !N_of_list_bits_nil.
    lia. }
  { rewrite !N_of_list_bits_cons, IHl1.
    rewrite Nat2N.inj_succ, N.pow_succ_r by lia.
    lia. }
Qed.

Local Close Scope N_scope.

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

Lemma N2Bv_sized_succ_double sz n :
  N2Bv_sized (S sz) (N.succ_double n) = (true :: N2Bv_sized sz n)%vector.
Proof. destruct n; reflexivity. Qed.

Lemma N2Bv_sized_double sz n :
  N2Bv_sized (S sz) (N.double n) = (false :: N2Bv_sized sz n)%vector.
Proof. destruct n; reflexivity. Qed.

Lemma Bv2N_cons {n : nat} (b : bool) (v : Bvector.Bvector n) :
  Bv2N (b :: v)%vector = (if b then N.succ_double (Bv2N v) else N.double (Bv2N v))%N.
Proof. reflexivity. Qed.

Lemma Bv2N_inj {n} (x y : Bvector.Bvector n) : Bv2N x = Bv2N y -> x = y.
Proof.
  cbv [Bvector.Bvector] in *.
  revert x y; induction n; intros x y ?; [ apply nil_eq | ].
  rewrite (eta x), (eta y) in *. cbn [Bv2N] in *.
  destruct (Vector.hd x), (Vector.hd y);
    repeat lazymatch goal with
           | H : N.succ_double _ = N.succ_double _  |- _ =>
             apply N.succ_double_inj in H
           | H : N.double _ = N.double _  |- _ =>
             apply N.double_inj in H
           | H : N.succ_double _ = N.double _  |- _ =>
             apply N.succ_double_double_neq in H; tauto
           | H : N.double _ = N.succ_double _ |- _ => symmetry in H
           end; [ | ].
  all:rewrite (IHn (Vector.tl x) (Vector.tl y)) by auto.
  all:reflexivity.
Qed.

Hint Rewrite @Bv2N_N2Bv @Bv2N_cons @Bv2N_Bvect_false @Bv2N_append
     using solve [eauto] : push_Bv2N.
Hint Rewrite @Bv2N_N2Bv_sized using lia : push_Bv2N.

Hint Rewrite @N2Bv_sized_double @N2Bv_sized_succ_double @N2Bv_sized_Nsize
     using solve [eauto] : push_N2Bv_sized.

Lemma Bv2N_N2Bv_sized_testbit sz n i :
  N.testbit (Bv2N (N2Bv_sized sz n)) i = if (i <? N.of_nat sz)%N
                                         then N.testbit n i else false.
Proof.
  revert i sz; induction n using N.binary_ind; intros;
    (destruct sz; [ |  pose proof (N.pow_gt_1 2 (N.of_nat (S sz)) ltac:(lia) ltac:(lia)) ]);
    repeat match goal with
           | |- context [N2Bv_sized 0 ?n] => eapply case0 with (v:=N2Bv_sized 0 n)
           | |- context [N.ltb ?a ?b] => case_eq (N.ltb a b);
                                         [ rewrite N.ltb_lt | rewrite N.ltb_ge ];
                                         intros
           | |- context [N.eqb ?a ?b] => case_eq (N.eqb a b);
                                         [ rewrite N.eqb_eq | rewrite N.eqb_neq ];
                                         intros
           | _ => first [ rewrite IHn
                       | progress autorewrite with push_Bv2N push_N2Bv_sized push_Ntestbit
                       | reflexivity
                       | lia ]
           end.
Qed.
Hint Rewrite Bv2N_N2Bv_sized_testbit using solve [eauto] : push_Ntestbit.

Lemma Bv2N_N2Bv_sized_modulo sz n :
  Bv2N (N2Bv_sized sz n) = (n mod 2 ^ (N.of_nat sz))%N.
Proof.
  apply N.bits_inj; intro. autorewrite with push_Ntestbit. reflexivity.
Qed.

Lemma N2Bv_sized_ones_step sz :
  N2Bv_sized (S sz) (N.ones (N.of_nat (S sz)))
  = (true :: N2Bv_sized sz (N.ones (N.of_nat sz)))%vector.
Proof.
  rewrite N.ones_succ. autorewrite with push_N2Bv_sized.
  reflexivity.
Qed.
Hint Rewrite N2Bv_sized_ones_step using solve [eauto] : push_N2Bv_sized.

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

Lemma P2Bv_sized_cons n p :
  P2Bv_sized (S n) p = (match p with
                        | (p0~1)%positive => true :: P2Bv_sized n p0
                        | (p0~0)%positive => false :: P2Bv_sized n p0
                        | 1%positive => true :: Bvector.Bvect_false n
                        end)%vector.
Proof. reflexivity. Qed.

Lemma P2Bv_sized_shiftout n p :
  Vector.shiftout (P2Bv_sized (S n) p) = P2Bv_sized n p.
Proof.
  revert p; induction n; [ destruct p; reflexivity | ].
  intros. destruct p.
  all:rewrite P2Bv_sized_cons with (n:=S n).
  all:cbv [Bvector.Bvect_false].
  all:rewrite !shiftout_cons, ?shiftout_const.
  all:rewrite ?IHn.
  all:reflexivity.
Qed.

Lemma N2Bv_sized_shiftout n x :
  Vector.shiftout (N2Bv_sized (S n) x) = N2Bv_sized n x.
Proof.
  destruct x; [ apply shiftout_const | ].
  apply P2Bv_sized_shiftout.
Qed.

Lemma P2Bv_sized_last n p :
  Vector.last (P2Bv_sized (S n) p) = Pos.testbit_nat p n.
Proof.
  revert p; induction n; [ destruct p; reflexivity | ].
  intros. rewrite P2Bv_sized_cons with (n:=S n).
  destruct p.
  all:cbv [Bvector.Bvect_false].
  all:rewrite !last_cons, ?last_const.
  all:rewrite ?IHn.
  all:reflexivity.
Qed.

Lemma N2Bv_sized_last n x :
  Vector.last (N2Bv_sized (S n) x) = N.testbit_nat x n.
Proof.
  destruct x; [ apply last_const | ].
  apply P2Bv_sized_last.
Qed.

Hint Rewrite @N2Bv_sized_Bv2N using solve [eauto] : push_N2Bv_sized.
Hint Rewrite @N2Bv_sized_Bv2N using solve [eauto] : pull_N2Bv_sized.

Ltac bitvec_to_N :=
  apply Bv2N_inj; rewrite ?Bv2N_N2Bv_sized_modulo.

Lemma N2Bv_sized_add_idemp_r sz x y :
  N2Bv_sized sz (x + Bv2N (N2Bv_sized sz y)) = N2Bv_sized sz (x + y).
Proof.
  bitvec_to_N.
  rewrite N.add_mod_idemp_r by (apply N.pow_nonzero; lia).
  reflexivity.
Qed.
Hint Rewrite @N2Bv_sized_add_idemp_r using solve [eauto] : pull_N2Bv_sized.

Lemma N2Bv_sized_add_idemp_l sz x y :
  N2Bv_sized sz (Bv2N (N2Bv_sized sz x) + y) = N2Bv_sized sz (x + y).
Proof.
  bitvec_to_N.
  rewrite N.add_mod_idemp_l by (apply N.pow_nonzero; lia).
  reflexivity.
Qed.
Hint Rewrite @N2Bv_sized_add_idemp_l using solve [eauto] : pull_N2Bv_sized.

Theorem Bv_span {n} (a : Vector.t bool n) :
  InV a (Vector.map (fun k => N2Bv_sized n (N.of_nat k)) (vseq 0 (2 ^ n))).
Proof.
  apply InV_map_iff.
  induction a; [ | ].
  { apply ex_intro with (x:=0).
    split; [trivial | ].
    left. trivial. }
  { inversion IHa as [ x H ].
    destruct h; [ | ].
    { apply ex_intro with (x:=S(2*x)).
      split; destruct H as [H0]; [ | ].
      { rewrite Nat2N.inj_succ_double.
        rewrite N2Bv_sized_succ_double.
        rewrite H0.  trivial. }
      { apply InV_seq. apply InV_seq in H.
        cbn in H. cbn. lia. }
    }
    { apply ex_intro with (x:=2*x).
      split; destruct H ; [ | ].
      { rewrite Nat2N.inj_double.
        rewrite N2Bv_sized_double.
        rewrite H. trivial. }
      { apply InV_seq. apply InV_seq in H0.
        cbn. lia. }
    }
  }
Qed.

Theorem Bv_orthonormal {n} i j :
  (i < 2^ (N.of_nat n))%N ->
  (j < 2^ (N.of_nat n))%N ->
  (N2Bv_sized n i) = (N2Bv_sized n j)
  <-> i = j.
Proof.
  split; [ | ].
  { intros vec_eq.
    apply f_equal with (f:=Bv2N) in vec_eq.
    rewrite Bv2N_N2Bv_sized in vec_eq; [ | assumption ].
    rewrite Bv2N_N2Bv_sized in vec_eq; [ assumption | assumption ].
  }
  { intros. apply f_equal. assumption. }
Qed.
