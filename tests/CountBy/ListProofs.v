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

From Coq Require Import NArith.NArith Arith.PeanoNat Lists.List.
Require Import Coq.Bool.Bvector.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import coqutil.Tactics.Tactics.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.Acorn.AcornNew.
Require Import Cava.Acorn.IdentityNew.
Require Import Cava.Acorn.CombinationalProperties.
Require Import Cava.Lib.UnsignedAdders.

Require Import Tests.CountBy.CountBy.

Existing Instance CombinationalSemantics.

Definition bvadd {n} (a b : Bvector n) : Bvector n :=
  N2Bv_sized n (Bv2N a + Bv2N b).

Definition bvsum {n} (l : list (Bvector n)) : Bvector n :=
  fold_left bvadd l (N2Bv_sized n 0).

Definition countBySpec (i : list (Bvector 8)) : list (Bvector 8) :=
  map (fun t => bvsum (firstn t i)) (seq 1 (length i)).

Lemma addNCorrect n (a b : Bvector n) :
  unIdent (addN (a, b)) = bvadd a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : simpl_ident.

(*
Lemma countForkCorrect:
  forall (i : Bvector 8) (s : Bvector 8),
     ((addN >=> fork2) ([i], [s]))
    = (addNSpec [i] [s], addNSpec [i] [s]).
Proof.
  intros; cbv [mcompose].
  cbn [bind ret monad CombinationalSemantics
            Monad_ident].
  rewrite fork2Correct, !addNCorrect;
  reflexivity.
Qed.
Hint Rewrite countForkCorrect using solve [eauto] : seqsimpl.
*)
Lemma countByCorrect: forall (i : list (Bvector 8)),
    multistep countBy i = countBySpec i.
Proof.
  intros; cbv [countBy].
  cbv [countBySpec multistep].
  destruct i; [ reflexivity | ].
  cbn [interp reset_state Loop].
  repeat first [ destruct_pair_let | progress simpl_ident ].
  eapply (loopDelayS_invariant (B:=Vec Bit 8)) with
      (I:=fun t acc => acc = countBySpec (firstn t i)).
  { (* invariant holds at start *)
    reflexivity. }
  { (* invariant holds through body *)
    cbv zeta. intros; subst. seqsimpl.
    cbv [addNSpec countBySpec bvsum map2].
    rewrite firstn_succ_snoc with (d:=N2Bv_sized 8 0) by length_hammer.
    autorewrite with push_list_fold.
    cbv [seqType Signal.combType Bvector] in *.
    repeat first [ rewrite Nat.add_1_r
                 | rewrite seq_S, map_app; cbn [map]
                 | progress cbn [repeat app]
                 | progress seqsimpl
                 | progress autorewrite with push_length natsimpl
                                             push_list_fold push_firstn ].
    f_equal.
    { apply map_ext_in; intros.
      match goal with H : _ |- _ => apply in_seq in H end.
      autorewrite with push_length natsimpl push_firstn push_list_fold.
      reflexivity. }
    { cbv [bvadd]. rewrite N.add_comm.
      destruct t; autorewrite with push_nth push_firstn push_list_fold natsimpl;
        reflexivity. } }
  { (* invariant implies postcondition *)
    intros; seqsimpl; subst.
    rewrite firstn_all; reflexivity. }
Qed.
