Require Import List.
Import ListNotations.
Require Import Nat Arith Lia.


Definition nat_to_pair (n:nat) : bool * bool :=
  match n with
  | 0 => (false, false)
  | 1 => (false, true)
  | 2 => (true, false)
  | 3 => (true, true)
  | _ => (false, false)
  end.
  
Definition pair_to_nat (p:bool * bool) : nat :=
  match p with
  | (false, false) => 0
  | (false, true) => 1
  | (true, false) => 2
  | (true, true) => 3
  end.

Lemma nat_to_pair_correct : forall (n:nat), n < 4 -> pair_to_nat (nat_to_pair n) = n.
Proof.
  intros n H.
  repeat (destruct n; [reflexivity |]).
  lia.
Qed.  


(* Option 2: More general, list representation *)
Definition nat_to_bits (n:nat) : list bool  :=
  match n with
  | 0 => []
  | 1 => [true]
  | 2 => [true; false]
  | 3 => [true; true]
  | _ => []
  end.

(*
    [ b3 ; b2 ; b1 ] ==  000 b3 b2 b1
 *)
Fixpoint bits_to_nat (bits : list bool) : nat :=
  match bits with
  | [] =>  0
  | b::bs => (shiftl (Nat.b2n b) (length bs)) + (bits_to_nat bs)
  end.

Eval compute in (bits_to_nat [true;true;false]).
Eval compute in (bits_to_nat [false;true;true;true;true]).


Lemma simple_to_bits_correct : forall n, n < 4 -> bits_to_nat (nat_to_bits n) = n.
Proof.
  intros n H.
  repeat (destruct n; [reflexivity|]).
  lia.
Qed.




(*
  The list-of-bits representation is not canonical because leading
  0's don't contribute to the final value.  Therefore we can 
  put the list of bits into canonical form by trimming leading 
  0's.
*)
Fixpoint canonicalize_bits (bits : list bool) : list bool :=
  match bits with
  | [] => []
  | true::_ => bits
  | false::bs => canonicalize_bits bs
  end.


(* The coq library has some utilities for testing the bits of a nat.  See [testbit]. *)
Definition low_bit (n:nat) : bool := testbit n 0.

Eval compute in (low_bit 7).


(*
  The recursion structure for converting a nat to bits is based on
  division by two / bit-shifting, which isn't purely structural on the
  Zero + Successor version of nats.  One way around that is to define 
  a slightly different recursion principle that folds by div2.

  It may be worth checking out BinNat too.
 *)
(* Annoyingly PeanoNat.lt_wf_0 doesn't compute, so I have to define my own verions here.
   I use the well-foundness of lt to say that recursion by div2 terminates.
*)
Lemma lt_wf : well_founded lt.
Proof.
  apply well_founded_lt_compat with (f := id).
  tauto.
Defined.

(* This version of fold is specialized to dissecting natural numbers bitwise.
   When traversing over a natural number n, the [combine] function takes (div2
   n), the lower bit of n and the recursive fold result from (div2 n). *)
Definition fold_shift_nat {A} (base: A) (combine: nat -> bool -> A -> A) : nat -> A.
  refine (Fix lt_wf (fun _ => A)
              (fun (n:nat) f =>
                 if le_lt_dec n 0
                 then base
                 else combine (div2 n) (low_bit n) (f (div2 n) (PeanoNat.Nat.lt_div2 _ _)))).
  exact l.
Defined.

(* Now we can define nat_to_bits for general natural numbers: *)
Definition nat_to_bits' (n:nat) : list bool :=
  fold_shift_nat [] (fun x b l => l++[b]) n.

Eval compute in (nat_to_bits' 3).
Eval compute in (nat_to_bits' 6).


(* To prove correctness of nat_to_bits' I need a helper lemma. *)
Lemma bits_to_nat_app : forall u l, bits_to_nat (u ++ l) = (bits_to_nat u) * (shiftl 1 (length l)) + (bits_to_nat l).
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


Lemma nat_to_bits'_correct : forall n, bits_to_nat (nat_to_bits' n) = n.
Proof.
  induction n using lt_wf_ind.
  unfold nat_to_bits'.
  unfold fold_shift_nat. rewrite Fix_eq.
  - destruct (le_lt_dec n 0).
    + assert (n = 0). lia. subst. simpl. reflexivity.
    + rewrite bits_to_nat_app.
      unfold nat_to_bits' in H.
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
      
