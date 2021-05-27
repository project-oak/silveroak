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

Require Import Cava.Cava.
Require Import Cava.CavaProperties.
Require Import Tests.AccumulatingAdderEnable.AccumulatingAdderEnable.

Definition bvadd {n} (a b : Signal.combType (Vec Bit n)) : Signal.combType (Vec Bit n) :=
  N2Bv_sized n (Bv2N a + Bv2N b).

Definition bvzero {n} : Signal.combType (Vec Bit n) := N2Bv_sized n 0.

Definition bvsum {n} (l : list (Bvector n)) : Bvector n :=
  fold_left bvadd l (N2Bv_sized n 0).

Definition accumulatingAdderEnableSpec
           (i : list (combType (Vec Bit 8) * combType Bit))
  : list (combType (Vec Bit 8)) * combType (Vec Bit 8) :=
  fold_left
    (fun acc_st v_en =>
       let sum := bvadd (snd acc_st) (fst v_en) in
       (fst acc_st ++ [sum], if (snd v_en : bool) then sum else snd acc_st))
    i ([], bvzero).

Lemma addNCorrect n (a b : Vector.t bool n) :
  addN (a, b) = bvadd a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : simpl_ident.

Lemma bvadd_comm {n} a b : @bvadd n a b = bvadd b a.
Proof. cbv [bvadd]. rewrite N.add_comm. reflexivity. Qed.

Lemma accumulatingAdderEnableSpec_snoc xs x :
  accumulatingAdderEnableSpec (xs ++ [x]) =
  let acc_st := accumulatingAdderEnableSpec xs in
  let sum := bvadd (snd acc_st) (fst x) in
  (fst acc_st ++ [sum], if (snd x : bool) then sum else snd acc_st).
Proof.
  cbv [accumulatingAdderEnableSpec].
  autorewrite with pull_snoc. cbn [fst snd].
  reflexivity.
Qed.

Lemma accumulatingAdderEnableCorrect (i : list (Bvector 8 * bool)) :
  simulate accumulatingAdderEnable i = fst (accumulatingAdderEnableSpec i).
Proof.
  intros; cbv [accumulatingAdderEnable]. autorewrite with push_simulate.
  cbn [step reset_state]. cbv [mcompose]. simpl_ident.
  eapply fold_left_accumulate_invariant_seq
    with (I:=fun t st acc =>
               snd st = snd (accumulatingAdderEnableSpec (firstn t i))
               /\ acc = fst (accumulatingAdderEnableSpec (firstn t i)))
         (P:=fun x => x = fst (accumulatingAdderEnableSpec i)).
  { (* invariant holds after first step *)
    split; reflexivity. }
  { (* invariant holds through body *)
    cbv zeta. intros ? ? ? d; intros; logical_simplify; subst.
    repeat destruct_pair_let; cbn [fst snd]. simpl_ident.
    rewrite firstn_succ_snoc with (d0:=d) by length_hammer.
    rewrite accumulatingAdderEnableSpec_snoc. cbn [fst snd].
    lazymatch goal with H : _ = snd (accumulatingAdderEnableSpec _) |- _ =>
                        rewrite H end.
    rewrite bvadd_comm. split; reflexivity. }
  { (* invariant implies postcondition *)
    intros; logical_simplify; subst.
    rewrite firstn_all; reflexivity. }
Qed.
