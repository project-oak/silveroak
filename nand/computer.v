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

Definition g_half_adder(a b : bool) : bool * bool := (g_and a b, g_xor a b).

Definition p_half_adder(a b : nat) : nat := a + b.

Definition p_bits(a : bool * bool) : nat :=
  match a with
  | (true, true) => 3
  | (true, false) => 2
  | (false, true) => 1
  | (false, false) => 0
  end.

Definition p_bit(a : bool) : nat := if a then 1 else 0.

Lemma half_adder_equiv :
  forall (a b : bool), p_bits (g_half_adder a b) = p_half_adder (p_bit a) (p_bit b).
Proof.
  intros a b.
  case a, b.
  all: reflexivity.
Qed.

Definition g_full_adder(a b c : bool) : bool * bool :=
  let (abh, abl) := g_half_adder a b in
  let (abch, abcl) := g_half_adder abl c in
  let (h, l) := g_half_adder abh abch in
  (l, abcl).

Definition p_adder(a b c : nat) : nat := a + b + c.

Lemma full_adder_equiv :
  forall (a b c : bool), p_bits (g_full_adder a b c) = p_adder (p_bit a) (p_bit b) (p_bit c).
Proof.
  intros a b c.
  case a, b, c.
  all: reflexivity.
Qed.

Definition g_bit2_adder(a1 a0 b1 b0 c : bool) : bool * bool * bool :=
  let (h0, l0) := g_full_adder a0 b0 c in
  let (h1, l1) := g_full_adder a1 b1 h0 in
  (h1, l1, l0).

Definition p_bits3(a : bool*bool*bool) : nat :=
  match a with
  | (b, c, d) => p_bits (b, c) * 2 + p_bit d
  end.

Lemma bit2_adder_equiv :
  forall (a1 a0 b1 b0 c : bool), p_bits3 (g_bit2_adder a1 a0 b1 b0 c) = p_adder (p_bits (a1, a0)) (p_bits (b1, b0)) (p_bit c).
Proof.
  intros a1 a0 b1 b0 c.
  case a1, a0, b1, b0, c.
  all: reflexivity.
Qed.

Require Import List.

Fixpoint g_bitn_adder(n : nat) (a b : list bool) (c : bool) : list bool :=
  match n with
    | 0 => nil
    | 1 => let (h, l) := g_full_adder (hd false a) (hd false b) c in
           l::h::nil
    | S n' => let (h, l) := g_full_adder (hd false a) (hd false b) c in
              let r := g_bitn_adder n' (tl a) (tl b) h in
              l::r
      (* let (h, l) := g_full_adder (last a false) (last b false) c in
              let r := g_bitn_adder n' (removelast a) (removelast b) h in
              r ++ l::nil *)
  end.

Fixpoint p_lbits(b : list bool) : nat :=
  match b with
    | nil => 0
    | b0::t => (p_bit b0) + 2 * p_lbits t
  end.

Lemma bitn2_adder_equiv :
  forall (a1 a0 b1 b0 c : bool), p_lbits (g_bitn_adder 2 (a0::a1::nil) (b0::b1::nil) c) =  p_adder (p_bits (a1, a0)) (p_bits (b1, b0)) (p_bit c).
Proof.
  intros a1 a0 b1 b0 c.
  case a1, a0, b1, b0, c.
  all: reflexivity.
Qed.

(* proof due to Jade *)
Require Import Coq.micromega.Lia.

Lemma p_bit_to_bits a :
  p_bit (snd a) = p_bits a - 2 * p_bit (fst a).
Proof.
  destruct a as [b1 b2].
  destruct b1, b2.
  all: reflexivity.
Qed.

Lemma fst_bit_le_bits a :
 2 * p_bit (fst a) <= p_bits a.
Proof.
  destruct a as [b1 b2].
  case b1, b2.  (* can also use destruct *)
  all: cbn.
  all: lia.
Qed.

Lemma bitn_adder_is_adder :
  forall (n : nat) (a b : list bool) (c : bool),
    length a = (S n) -> length b = (S n) ->
    p_lbits (g_bitn_adder (S n) a b c) = p_adder (p_lbits a) (p_lbits b) (p_bit c).
Proof.
  induction n.
  all: intros a b c.
  all: destruct a.
  all: destruct b.
  all: cbn [length].
  all: try congruence. (* gets rid of length mismatches *)
  all: cbn [g_bitn_adder].
  all: intros.
  { (* n = 0 case *)
    (* gets rid of let '(h, l) := g_full_adder ... in *)
    match goal with
    | |- context [let '(_, _) := ?x in _] =>
      rewrite (surjective_pairing x)
    end.
    (* prove that lists with length 0 are nil *)
    repeat match goal with
           | H : S (length ?x) = 1 |- _ =>
             destruct x; [clear H|cbn [length] in H; congruence]
           end.
    cbn [p_lbits g_bitn_adder] in *.
    cbn [hd tl].
    rewrite (p_bit_to_bits (g_full_adder _ _ _)).
    (* need to show subtraction doesn't underflow for [lia]*)
    match goal with |- context [ p_bits ?x - ?y ] =>
                    assert (y <= p_bits x) by apply fst_bit_le_bits end.
    rewrite full_adder_equiv in *.
    cbv [p_adder] in *.
    lia. }
  { (* gets rid of let '(h, l) := g_full_adder ... in *)
    match goal with
    | |- context [let '(_, _) := ?x in _] =>
      rewrite (surjective_pairing x)
    end.
    destruct n.
    { (* n = 1 case *)
      cbn [p_lbits g_bitn_adder] in *.
      rewrite IHn by (cbn [length tl]; lia).
      cbn [hd tl].
      rewrite (p_bit_to_bits (g_full_adder _ _ _)).
      (* need to show subtraction doesn't underflow for [lia]*)
      match goal with |- context [ p_bits ?x - ?y ] =>
                      assert (y <= p_bits x) by apply fst_bit_le_bits end.
      rewrite full_adder_equiv in *.
      cbv [p_adder] in *.
      lia. }
    { (* n > 1 case -- proof is exactly the same *)
      cbn [p_lbits g_bitn_adder] in *.
      rewrite IHn by (cbn [length tl]; lia).
      cbn [hd tl].
      rewrite (p_bit_to_bits (g_full_adder _ _ _)).
      (* need to show subtraction doesn't underflow for [lia] *)
      match goal with |- context [ p_bits ?x - ?y ] =>
                      assert (y <= p_bits x) by apply fst_bit_le_bits end.
      rewrite full_adder_equiv in *.
      cbv [p_adder] in *.
      lia. } }
Qed.

Definition g_add16(a b : list bool) (c : bool) := g_bitn_adder 16 a b c.

(* TODO: define and prove general incrementer *)

Definition g_inc16(a : list bool) : list bool := g_add16 a (false::false::false::false::false::false::false::false::false::false::false::false::false::false::false::false::nil) true.

(* Note that this proof should not work! Presumably that will later come back to bite us so leave it for now *)

Lemma inc16_is_incrementer :
  forall (a : list bool),
    length a = 16 -> p_lbits (g_inc16 a) = p_lbits a + 1.
Proof.
  intros a.
  intros la.
  unfold g_inc16.
  unfold g_add16.
  rewrite bitn_adder_is_adder.
  simpl.
  unfold p_adder.
  rewrite <- plus_n_O.
  reflexivity.
  lia.
  simpl.
  reflexivity.
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

Definition g_inv16(a : list bool) := g_bitn_inverter 16 a.
