(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
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

(* Implement and prove the computer from http://nandgame.com/ *)

Require Import Bool.

Definition p_nand(a b : bool) : bool := negb (a && b).

Definition g_nand(a b : bool) : bool :=
  match (a, b) with
  (true, true) => false
  | (_, _) => true
end.

Lemma nand_equiv :
  forall (a b : bool), g_nand a b = p_nand a b.
Proof.
  intros.
  unfold p_nand.
  unfold g_nand.
  case a, b.
  all: simpl.
  all: reflexivity.
Qed.

Definition g_invert(a : bool) : bool := g_nand a a.

Definition p_invert(a : bool) : bool := negb a.

Lemma invert_equiv :
  forall (a : bool), g_invert a = p_invert a.
Proof.
  intros a.
  unfold g_invert.
  rewrite nand_equiv.
  unfold p_invert.
  unfold p_nand.
  rewrite andb_diag.
  reflexivity.
Qed.

Definition g_and(a b : bool) : bool := g_invert (g_nand a b).

Definition p_and(a b : bool) : bool := a && b.

Lemma and_equiv :
  forall (a b : bool), g_and a b = p_and a b.
Proof.
  intros a b.
  unfold g_and.
  unfold p_and.
  rewrite invert_equiv.
  rewrite nand_equiv.
  unfold p_invert.
  unfold p_nand.
  rewrite negb_involutive.
  reflexivity.
Qed.

Definition g_or(a b : bool) : bool := g_nand (g_invert a) (g_invert b).

Definition p_or(a b : bool) : bool := a || b.

Lemma or_equiv :
  forall (a b : bool), g_or a b = p_or a b.
Proof.
  intros a b.
  unfold g_or.
  unfold p_or.
  rewrite invert_equiv.
  rewrite invert_equiv.
  rewrite nand_equiv.
  unfold p_nand.
  unfold p_invert.
  rewrite negb_andb.
  rewrite negb_involutive.
  rewrite negb_involutive.
  reflexivity.
Qed.

Definition g_xor(a b : bool) : bool := let nab := g_nand a b in g_nand (g_nand a nab) (g_nand nab b).

Definition p_xor(a b : bool) : bool := xorb a b.

Lemma xor_equiv :
  forall (a b : bool), g_xor a b = p_xor a b.
Proof.
  intros a b.
  case a, b.
  all: reflexivity.
Qed.

(* All bit lists are little endian, so a function returning a carry returns that last for consistency *)

Require Import List.

Definition p_bit_to_nat(a : bool) : nat := if a then 1 else 0.

Fixpoint p_bits_to_nat(b : list bool) : nat :=
  match b with
    | nil => 0
    | b0::t => (p_bit_to_nat b0) + 2 * p_bits_to_nat t
  end.

(* conveniences for dealing with carries *)
Definition p_bitsc_to_nat (b : list bool) (c : bool) : nat := p_bits_to_nat (b ++ c::nil).
Definition p_bitc_to_nat (b c : bool) : nat := p_bits_to_nat (b::c::nil).

Definition g_half_adder(a b : bool) : bool * bool := (g_xor a b, g_and a b).

Definition p_half_adder(a b : nat) : nat := a + b.

(* Definition p_bits(a : bool * bool) : nat :=
  match a with
  | (true, true) => 3
  | (true, false) => 2
  | (false, true) => 1
  | (false, false) => 0
  end. *)

Lemma half_adder_equiv :
  forall (a b : bool), let (r, c) := g_half_adder a b in p_bitc_to_nat r c = p_half_adder (p_bit_to_nat a) (p_bit_to_nat b).
Proof.
  intros a b.
  case a, b.
  all: reflexivity.
Qed.

Definition g_full_adder(a b c : bool) : bool * bool :=
  let (abl, abh) := g_half_adder a b in
  let (abcl, abch) := g_half_adder abl c in
(*  let (l, h) := g_half_adder abh abch in
  (abcl, l). or.. *)
  (abcl, g_or abh abch).  (* should be g_xor, but the true, true case is impossible and g_or is cheaper *)

Compute g_full_adder true true true.

Definition p_adder(a b c : nat) : nat := a + b + c.

Lemma full_adder_equiv :
  forall (a b c : bool), let r := g_full_adder a b c in p_bits_to_nat (fst r::snd r::nil) = p_adder (p_bit_to_nat a) (p_bit_to_nat b) (p_bit_to_nat c).
Proof.
  intros a b c.
  case a, b, c.
  all: simpl.  (* not needed, goes faster *)
  all: reflexivity.
Qed.

Definition g_bit2_adder(a0 a1 b0 b1 c : bool) : bool * bool * bool :=
  let (l0, h0) := g_full_adder a0 b0 c in
  let (l1, h1) := g_full_adder a1 b1 h0 in
  (l0, l1, h1).

(* Definition p_bits3(a : bool*bool*bool) : nat :=
  match a with
  | (b, c, d) => p_bits (b, c) * 2 + p_bit d
  end. *)

Compute g_bit2_adder true true true true true.

Lemma bit2_adder_equiv :
  forall (a1 a0 b1 b0 c : bool),
    let '(r0, r1, c') := g_bit2_adder a0 a1 b0 b1 c in
    p_bits_to_nat (r0::r1::c'::nil) = p_adder (p_bits_to_nat (a0::a1::nil)) (p_bits_to_nat (b0::b1::nil)) (p_bit_to_nat c).
Proof.
  intros a1 a0 b1 b0 c.
  case a1, a0, b1, b0, c.
  all: reflexivity.
Qed.

Fixpoint g_bitn_adder (a b : list bool) (c : bool) : list bool :=
  match a with
    | nil => nil
    | a0::nil => let (l, h) := g_full_adder (hd false a) (hd false b) c in
           l::h::nil
    | a0::t => let (l, h) := g_full_adder (hd false a) (hd false b) c in
              let r := g_bitn_adder t (tl b) h in
              l::r
      (* let (h, l) := g_full_adder (last a false) (last b false) c in
              let r := g_bitn_adder n' (removelast a) (removelast b) h in
              r ++ l::nil *)
  end.

Lemma bitn2_adder_equiv :
  forall (a1 a0 b1 b0 c : bool),
    p_bits_to_nat (g_bitn_adder (a0::a1::nil) (b0::b1::nil) c) =  p_adder (p_bits_to_nat (a0::a1::nil)) (p_bits_to_nat (b0::b1::nil)) (p_bit_to_nat c).
Proof.
  intros a1 a0 b1 b0 c.
  case a1, a0, b1, b0, c.
  all: reflexivity.
Qed.

(* original proof due to Jade, now heavily mangled *)
Require Import Coq.micromega.Lia.

Lemma p_bit_to_bits a:
  p_bit_to_nat (fst a) = p_bits_to_nat ((fst a)::(snd a)::nil) - 2 * p_bit_to_nat (snd a).
Proof.
  destruct a as [b1 b2].
  destruct b1, b2.
  all: reflexivity.
Qed.


Lemma snd_bit_le_bits a :
  2 * p_bit_to_nat (snd a) <= p_bits_to_nat ((fst a)::(snd a)::nil).
Proof.
  destruct a as [b1 b2].
  case b1, b2.  (* can also use destruct *)
  all: cbn.
  all: lia.
Qed.

Lemma SS_ne_1 :
  forall (n : nat),
    1 <> S (S n).
Proof.
  intros.
  lia.
Qed.

Lemma snd_adder_le_sum:
  forall (a b c : bool),
    2 * p_bit_to_nat (snd (g_full_adder a b c)) <= p_bit_to_nat a + p_bit_to_nat b + p_bit_to_nat c.
Proof.
  case a, b, c.
  all: simpl.
  all: lia.
Qed.

Lemma len_helper:
  forall (a b : list bool),
    S (length (true :: a)) = S (length b) -> S (length a) = length b.
Proof.
  intros a b.
  cbn [length].
  lia.
Qed.

Lemma bitn_adder_is_adder :
  forall (a b : list bool) (c : bool),
    0 < length a -> length a = length b ->
    p_bits_to_nat (g_bitn_adder a b c) = p_adder (p_bits_to_nat a) (p_bits_to_nat b) (p_bit_to_nat c).
Proof.
  induction a.
  all: intros b c.
  all: destruct b.
  all: cbn [length].
  all: try congruence. (* gets rid of length mismatches *)
  all: cbn [g_bitn_adder].
  all: intros.

  { (* a = nil case *)
    apply Lt.lt_0_neq in H.
    contradiction. }

  { (* gets rid of let '(h, l) := g_full_adder ... in *)
    match goal with
    | |- context [let '(_, _) := ?x in _] =>
      rewrite (surjective_pairing x)
    end.
    destruct a0.
    { (* length a0 = 1 case *)
      cbn [p_bits_to_nat g_bitn_adder] in *.
      cbn [hd tl].
      rewrite (p_bit_to_bits (g_full_adder _ _ _)).
      rewrite full_adder_equiv in *.
      cbv [p_adder] in *.
      rewrite <- mult_n_O with (n := 2).
      rewrite <- plus_n_O with (n := p_bit_to_nat a).
      rewrite <- plus_n_O with (n := p_bit_to_nat (snd (g_full_adder a b c))).
      rewrite <- PeanoNat.Nat.add_sub_swap.
      rewrite <- PeanoNat.Nat.add_sub_assoc.
      rewrite PeanoNat.Nat.sub_diag with (n := 2 * p_bit_to_nat (snd (g_full_adder a b c))).
      destruct b0.
      - simpl.
        rewrite <- plus_n_O.
        rewrite <- plus_n_O.
        reflexivity.
      - simpl in H0.
        apply SS_ne_1 in H0.
        contradiction.
      - reflexivity.
      - apply snd_adder_le_sum. }
    { (* length a0 > 1 case *)
      cbn [hd tl].
      all: case a, b1, b, c.
      all: cbv [g_full_adder g_half_adder g_xor g_nand g_or g_invert g_and fst snd].
      all: cbn [p_bits_to_nat p_bit_to_nat].
      all: unfold p_adder.
      all: rewrite IHa.
      all: unfold p_adder.
      all: simpl.
      all: try lia.
      all: apply len_helper.
      all: apply H0. }
    }
Qed.

(* a one as a list of bools *)
Fixpoint g_one (l : nat) : list bool :=
  match l with
  | 0 => nil
  | 1 => true::nil
  | S l' => g_one l' ++ false::nil
  end.

(* Naive incrementer - just use an adder to add one *)
Definition g_inc (a : list bool) : list bool :=
  g_bitn_adder a (g_one (length a)) false.

Definition p_inc (a : nat) : nat :=
  a + 1.

Lemma one_is_one_longer :
  forall (l : nat),
    0 < l -> g_one(S l) = g_one(l) ++ false::nil.
Proof.
  intros.
  simpl.
  apply Lt.lt_0_neq in H.
  destruct l.
  - contradiction.
  - reflexivity.
Qed.

Lemma adding_false_is_the_same :
  forall (l: list bool),
    p_bits_to_nat (l ++ false::nil) = p_bits_to_nat l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - case a.
    all: simpl.
    all: rewrite <- IHl.
    all: reflexivity.
Qed.

Lemma one_is_one :
  forall (l : nat),
    p_bits_to_nat (g_one (S l)) = 1.
Proof.
  intros l.
  induction l.
  { (* l = 1 *)
    reflexivity. }
  { (* l > 1 *)
    rewrite one_is_one_longer with (l := S l).
    (* prove side condition *)
    2: apply PeanoNat.Nat.lt_0_succ.
    rewrite adding_false_is_the_same.
    apply IHl. }
Qed.

Lemma length_of_one :
  forall (n : nat),
   length (g_one (S n)) = S n.
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - rewrite one_is_one_longer.
    (* side condition *)
    2: apply PeanoNat.Nat.lt_0_succ.
    rewrite app_length.
    rewrite IHn.
    rewrite PeanoNat.Nat.add_1_r.
    reflexivity.
Qed.

Lemma inc_is_inc :
  forall (a : list bool),
    0 < length a -> p_bits_to_nat (g_inc a) = p_inc (p_bits_to_nat a).
Proof.
  intros.
  unfold g_inc.
  rewrite bitn_adder_is_adder.
  { assert (exists n, length a = S n).
    { pose (witness := length a - 1).
      refine (ex_intro _ witness _).
      lia. }
    { simpl.
      unfold p_inc.
      unfold p_adder.
      destruct H0.
      rewrite H0.
      rewrite one_is_one.
      lia. }
  }
  { apply H. }
  { assert (exists n, length a = S n).
    { pose (witness := length a - 1).
      refine (ex_intro _ witness _).
      lia. }
    { destruct H0.
      rewrite H0.
      rewrite length_of_one.
      reflexivity. }
  }
Qed.

Fixpoint g_bitn_inverter (n : nat) (a : list bool) : list bool :=
  match n with
  | 0 => nil
  | S n => g_invert (hd false a) :: g_bitn_inverter n (tl a)
  end.

Definition p_inverter (a : list bool) : list bool := map negb a.

Lemma invert_negb (a : bool) : g_invert a = negb a.
Proof. destruct a; reflexivity. Qed.

Lemma bitn_inverter_is_inverter :
  forall (n: nat) (a : list bool),
    length a = n -> g_bitn_inverter (length a) a = p_inverter a.
Proof.
  induction n.
  all: intros a.
  intros la.
  rewrite la.
  unfold g_bitn_inverter.
  unfold p_inverter.
  rewrite length_zero_iff_nil in la.
  rewrite la.
  reflexivity.

  (* Proof of second case by Jade *)
  intros la.
  destruct a as [|b a']. (* Just "destruct a." will work -- the rest lets me name the new variables *)
  { (* first case : a = nil, which is impossible since length nil <> S n *) (* also note that the goal can be proved with reflexivity instead *)
    cbn [length] in la.
    congruence. (* 0 = S n is not possible *) }
  { (* second case : a = b :: a' *)
    (* now run one step of the inverters *)
    cbn [length hd tl g_bitn_inverter p_inverter map].
    (* use inductive hypothesis *)
    rewrite <-IHn.
    (* prove side condition: length a' = n *)
    2 : { cbn [length] in la. inversion la. reflexivity. }
    (* now we have to prove g_invert b = negb b -- use helper lemma *)
    rewrite invert_negb.
    reflexivity. }
Qed.

Definition g_inv16 := g_bitn_inverter 16.

Print g_inv16.
