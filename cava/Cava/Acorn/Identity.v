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
Require Import Coq.Vectors.Vector.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadLaws.
Require Import Cava.Signal.
Require Import Cava.Tactics.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.
Require Import Cava.Lib.BitVectorOps.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.CombinationalMonad.
Require Import Cava.Acorn.Combinators.
Import VectorNotations ListNotations.
Open Scope list_scope.

Existing Instance CircuitSemantics.


Section MapT.
  Lemma mapT_vector_ident {A B n} (f : A -> ident B) (v : Vector.t A n) :
    unIdent (mapT_vector f v) = map (fun a => unIdent (f a)) v.
  Proof.
    induction v; intros; [ reflexivity | ].
    cbn. rewrite IHv. reflexivity.
  Qed.
End MapT.
Hint Rewrite @mapT_vector_ident using solve [eauto] : simpl_ident.

Section PeelUnpeel.
  Lemma peelVecList_cons_cons {A n} (a : combType A) (v : combType (Vec A n)) :
    peelVecList [(a :: v)%vector] = ([a]%list :: peelVecList [v])%vector.
  Proof.
    cbv [peelVecList indexConstBoolList]. cbn [List.map Vector.map].
    apply to_list_inj. autorewrite with push_to_list.
    rewrite <-cons_seq, <-seq_shift. cbn [List.map]. rewrite List.map_map.
    cbn. autorewrite with natsimpl.
    reflexivity.
  Qed.

  (* Useful for unpeel *)
  Lemma max_length_same_length {A n} (v : Vector.t (list A) n) m len:
    (forall l, InV l v -> length l = len) -> n <> 0 -> m <= len ->
    fold_left PeanoNat.Nat.max m (map (@length _) v) = len.
  Proof.
    revert m; induction n; intros; [ congruence | ].
    rewrite (eta v) in *. cbn [Vector.map InV] in *.
    autorewrite with vsimpl in *.
    destruct (PeanoNat.Nat.eq_dec n 0);
      subst; autorewrite with push_vector_fold vsimpl;
        repeat match goal with
               | Hin : forall l, _ -> length l = _ |- _ =>
                 rewrite Hin by (tauto || lia)
               | _ => rewrite IHn; [ | intros; try lia .. ]
               | _ => reflexivity
               | _ => lia
               end.
  Qed.

  Lemma peelVecList_length {A n} (v : seqType (Vec A n)) l :
    InV l (peelVecList v) -> length l = length v.
  Proof.
    cbv [peelVecList indexConstBoolList].
    rewrite InV_map_iff. destruct 1 as [? [? ?]].
    subst. autorewrite with push_length. reflexivity.
  Qed.

  Lemma unpeelVecList_cons_singleton {A n} (a : combType A) (v : Vector.t (seqType A) n) x :
    (forall l, InV l v -> length l = 1) -> n <> 0 -> unpeelVecList v = [x]%list ->
    unpeelVecList ([a]%list :: v)%vector = [(a :: x)%vector].
  Proof.
    cbv [unpeelVecList]; intros Hin ? Heq.
    rewrite max_length_same_length with (len:=1) in Heq by (lia || eauto).
    rewrite max_length_same_length with (len:=1)
      by (try lia; eauto; intros *; rewrite InV_cons_iff;
          destruct 1; subst; intros; eauto).
    cbn [List.map List.seq Vector.map List.nth] in *.
    inversion Heq; reflexivity.
  Qed.
End PeelUnpeel.

(* Lemmas about combinators specialized to the identity monad *)
Section Combinators.
  Lemma zipWith_unIdent {A B C : SignalType} n
        (f : seqType A * seqType B -> cava (seqType C))
        (spec : combType A -> combType B -> combType C)
        (va : combType (Vec A n)) (vb : combType (Vec B n)) :
    n <> 0 ->
    (forall a b, unIdent (f ([a], [b])) = [spec a b]) ->
    unIdent (@zipWith _ _ A B C n f [va] [vb])
    = [Vector.map2 spec va vb].
  Proof.
    cbv [zipWith Traversable.mapT Traversable_vector].
    cbn [peel unpeel monad CircuitSemantics].
    cbn [bind ret Monad_ident unIdent] in *.
    rewrite mapT_vector_ident.
    revert va vb; induction n; intros; [ lia | ].
    { rewrite (eta va), (eta vb).
      autorewrite with push_vcombine push_vector_map vsimpl.
      cbn [combType]  in *. rewrite !peelVecList_cons_cons.
      autorewrite with push_vcombine push_vector_map vsimpl.
      lazymatch goal with
      | Hspec : context [unIdent (f _)] |- _ =>
        rewrite Hspec
      end.
      fold combType.
      destruct (PeanoNat.Nat.eq_dec n 0).
      { subst n. eapply case0 with (v:=Vector.tl va).
        eapply case0 with (v:=Vector.tl vb).
        reflexivity. }
      cbv [seqType].
      erewrite unpeelVecList_cons_singleton; eauto; [ ].
      intros *. rewrite InV_map_iff.
      destruct 1 as [? [? ?]].
      subst.
      cbv [vcombine] in *.
      repeat match goal with
             | H : _ |- _ =>
               apply InV_map2_impl in H; destruct H as [? [? [? [? ?]]]]; subst
             | H : InV _ _ |- _ => apply peelVecList_length in H
             end.
      match goal with
      | |- context [f (?l1, ?l2)] =>
        destruct l1 as [| ? [|? ?] ];
          destruct l2 as [| ? [|? ?] ];
          cbn [length] in *; try lia
      end.
      lazymatch goal with
      | Hspec : context [unIdent (f _)] |- _ =>
        rewrite Hspec
      end.
      reflexivity. }
  Qed.
End Combinators.


Section Vectors.
  Lemma xorV_unIdent n a b :
    n <> 0 ->
    unIdent (@xorV _ _ n ([a],[b])) = [Vector.map2 xorb a b].
  Proof.
    intros. cbv [xorV]. cbn [fst snd].
    erewrite zipWith_unIdent; [ reflexivity | lia | ].
    intros; reflexivity.
  Qed.
End Vectors.

Instance MonadLaws_ident : MonadLaws Monad_ident.
Proof. econstructor; intros; exact eq_refl. Defined.

(* Automation to help simplify expressions using the identity monad *)
Create HintDb simpl_ident discriminated.
Hint Rewrite @zipWith_unIdent @xorV_unIdent
     using solve [eauto]: simpl_ident.
Ltac simpl_ident :=
  repeat
    first [ progress autorewrite with simpl_ident
          | erewrite map2_ext; [ | intros; progress simpl_ident;
                                   instantiate_app_by_reflexivity ]
          | erewrite map_ext; [ | intros; progress simpl_ident;
                                  instantiate_app_by_reflexivity ]
          | erewrite fold_left_ext; [ | intros; progress simpl_ident;
                                        instantiate_app_by_reflexivity ]
          | progress cbn [fst snd bind ret Monad_ident monad
                              CircuitSemantics unIdent] ].
