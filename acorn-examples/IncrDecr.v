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

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.CombinationalProperties.
Require Import Cava.Acorn.Identity.
Require Import Cava.BitArithmetic.
Require Import Cava.NatUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Lib.VecProperties.
Require Cava.Lib.Vec.
Import VectorNotations ListNotations MonadNotation.
Open Scope monad_scope.
Open Scope list_scope.

Section WithCava.
  Context `{semantics: Cava}.

  Definition half_adder (input : signal Bit * signal Bit)
  : cava (signal Bit * signal Bit) :=
    sum <- xor2 input ;;
    carry <- and2 input ;;
    ret (sum, carry).

  Definition half_subtractor (input : signal Bit * signal Bit)
    : cava (signal Bit * signal Bit) :=
    let '(x,y) := input in
    diff <- xor2 (x,y) ;;
    notx <- inv x ;;
    borrow <- and2 (notx, y) ;;
    ret (diff, borrow).

  (* increment a 4-bit vector *)
  Definition incr4 (input : signal (Vec Bit 4))
    : cava (signal (Vec Bit 4)) :=
    i0 <- indexConst input 0 ;;
    i1 <- indexConst input 1 ;;
    i2 <- indexConst input 2 ;;
    i3 <- indexConst input 3 ;;
    '(sum0, carry) <- half_adder (one, i0) ;;
    '(sum1, carry) <- half_adder (carry, i1) ;;
    '(sum2, carry) <- half_adder (carry, i2) ;;
    '(sum3, carry) <- half_adder (carry, i3) ;;
    packv [sum0;sum1;sum2;sum3]%vector.

  (* decrement a 4-bit vector *)
  Definition decr4 (input : signal (Vec Bit 4))
    : cava (signal (Vec Bit 4)) :=
    i0 <- indexConst input 0 ;;
    i1 <- indexConst input 1 ;;
    i2 <- indexConst input 2 ;;
    i3 <- indexConst input 3 ;;
    '(diff0, borrow) <- half_subtractor (i0, one) ;;
    '(diff1, borrow) <- half_subtractor (i1, borrow) ;;
    '(diff2, borrow) <- half_subtractor (i2, borrow) ;;
    '(diff3, borrow) <- half_subtractor (i3, borrow) ;;
    packv [diff0;diff1;diff2;diff3]%vector.

  Fixpoint incr' {sz} (carry : signal Bit)
    : signal (Vec Bit sz) -> cava (signal (Vec Bit sz)) :=
    match sz as sz0 return
          signal (Vec Bit sz0) -> cava (signal (Vec Bit sz0)) with
    | 0 => fun input => ret input
    | S sz' => fun input : signal (Vec Bit (S sz')) =>
                i0 <- Vec.hd input ;;
                rem <- Vec.tl input ;;
                '(sum0, carry) <- half_adder (carry, i0) ;;
                sum <- incr' carry rem ;;
                Vec.cons sum0 sum
    end.

  (* increments a bit vector of any length *)
  Definition incr {sz} (input : signal (Vec Bit sz)) : cava (signal (Vec Bit sz)) :=
    incr' one input.

  Fixpoint decr' {sz} (borrow : signal Bit)
    : signal (Vec Bit sz) -> cava (signal (Vec Bit sz)) :=
    match sz as sz0 return
          signal (Vec Bit sz0) -> cava (signal (Vec Bit sz0)) with
    | 0 => fun input => ret input
    | S sz' => fun input : signal (Vec Bit (S sz')) =>
                i0 <- Vec.hd input ;;
                rem <- Vec.tl input ;;
                '(diff0, borrow) <- half_subtractor (i0, borrow) ;;
                diff <- decr' borrow rem ;;
                Vec.cons diff0 diff
    end.

  (* decrements a bit vector of any length *)
  Definition decr {sz} (input : signal (Vec Bit sz)) : cava (signal (Vec Bit sz)) :=
    decr' one input.
End WithCava.

Section Proofs.
  Existing Instance CombinationalSemantics.

  Lemma half_adder_correct (x y : combType Bit) :
    unIdent (half_adder (x,y)) = (xorb x y, andb x y).
  Proof.
    cbv [half_adder and2 xor2 CombinationalSemantics].
    simpl_ident. reflexivity.
  Qed.
  Hint Rewrite half_adder_correct using solve [eauto] : simpl_ident.

  Lemma incr4_correct (input : combType (Vec Bit 4)) :
    unIdent (incr4 input) = N2Bv_sized 4 (Bv2N input + 1).
  Proof.
    cbv [incr4]. simpl_ident. boolsimpl.
    cbn [packv indexConst CombinationalSemantics].
    cbn [combType] in input. constant_bitvec_cases input.
    all:reflexivity.
  Qed.

  Lemma half_subtractor_correct (x y : combType Bit) :
    unIdent (half_subtractor (x,y)) = (xorb x y, andb (negb x) y).
  Proof.
    cbv [half_subtractor and2 xor2 CombinationalSemantics].
    simpl_ident; reflexivity.
  Qed.
  Hint Rewrite half_subtractor_correct using solve [eauto] : simpl_ident.

  Lemma decr4_correct (input : combType (Vec Bit 4)) :
    unIdent (decr4 input) = N2Bv_sized 4 (if (Bv2N input =? 0)%N then 15
                                          else Bv2N input - 1).
  Proof.
    cbv [decr4]. simpl_ident. boolsimpl.
    cbn [combType] in input. constant_bitvec_cases input.
    all:reflexivity.
  Qed.

  Lemma incr'_correct {sz} carry (input : combType (Vec Bit sz)) :
    unIdent (incr' carry input)
    = N2Bv_sized _ (Bv2N input + if carry then 1 else 0)%N.
  Proof.
    revert carry input; induction sz; intros; [ cbn; f_equal; solve [apply nil_eq] | ].
    cbn [incr']. simpl_ident.
    rewrite (eta input). autorewrite with vsimpl. repeat destruct_pair_let.
    rewrite IHsz. rewrite Bv2N_cons.
    destruct carry, (hd input); boolsimpl;
      rewrite ?N.add_0_r, ?N.double_succ_double, ?N.succ_double_succ;
      rewrite ?N2Bv_sized_double, ?N2Bv_sized_succ_double;
      reflexivity.
  Qed.

  Lemma incr_correct {sz} (input : combType (Vec Bit sz)) :
    unIdent (incr input) = N2Bv_sized _ (Bv2N input + 1).
  Proof. cbv [incr]. simpl_ident. apply incr'_correct. Qed.

  Lemma decr'_correct {sz} borrow (input : combType (Vec Bit sz)) :
    unIdent (decr' borrow input)
    = N2Bv_sized _ (if borrow
                    then if (Bv2N input =? 0)%N
                         then N.ones (N.of_nat sz)
                         else N.pred (Bv2N input)
                    else Bv2N input).
  Proof.
    revert borrow input; induction sz; intros; [ cbn; f_equal; solve [apply nil_eq] | ].
    cbn [decr']. simpl_ident.
    rewrite (eta input). autorewrite with vsimpl. repeat destruct_pair_let.
    rewrite IHsz. rewrite Bv2N_cons.
    destruct borrow, (Vector.hd input); boolsimpl;
      autorewrite with push_Bv2N push_N2Bv_sized;
      rewrite ?N.sub_0_r, ?N2Bv_sized_Bv2N;
      try reflexivity; [ | ].
    (* solve the majority of cases *)
    all:repeat match goal with
               | H : (?n = 0)%N |- _ => rewrite H
               | H : (N.succ_double ?n = 0)%N |- _ =>
                 rewrite N.succ_double_spec in H; lia
               | H : (N.double 0 <> 0)%N |- _ =>
                 cbn [N.double] in H; congruence
               | H1 : (?n <> 0)%N, H2 : (N.double ?n = 0)%N |- _ =>
                 rewrite N.double_spec in H2; lia
               | _ => first [ progress autorewrite with push_N2Bv_sized
                           | rewrite N2Bv_sized_Bv2N
                           | rewrite N.pred_sub, N.succ_double_double
                           | destruct_one_match
                           | reflexivity ]
               end.
    (* should only have one case left *)
    {  f_equal; rewrite <-N2Bv_sized_succ_double.
       rewrite !N.double_spec, !N.succ_double_spec, !N.pred_sub.
       f_equal; lia. }
  Qed.

  Lemma decr_correct {sz} (input : combType (Vec Bit sz)) :
    unIdent (decr input)
    = N2Bv_sized _ ( if (Bv2N input =? 0)%N
                     then 2 ^ (N.of_nat sz) - 1
                     else Bv2N input - 1)%N.
  Proof.
    cbv [decr]. rewrite decr'_correct.
    rewrite N.ones_equiv, !N.pred_sub. reflexivity.
  Qed.
End Proofs.
