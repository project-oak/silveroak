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

Require Import Cava.CavaProperties.

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
    { cbn. subst. apply Vector.In_cons_hd. }
    { cbn.
      apply Eqdep.EqdepTheory.inj_pair2 in H4.
      apply Vector.In_cons_tl.
      apply IHv.
      subst.
      trivial. }
  }
Qed.

Theorem In_list:
  forall n len start : nat, Vector.In n (vseq start len) <-> List.In n (seq start len).
Proof.
  induction len.
  { compute.
    split; intros; inversion H. }
  { split.
    { intros.
      inversion H.
      { left. trivial. }
      { apply Eqdep.EqdepTheory.inj_pair2 in H3.
        subst.
        right.
        apply IHlen.
        rewrite Nat.add_comm in H2.
        assumption. }
    }
    { cbn [In seq].
      intros [Hl | Hr].
      { subst. apply Vector.In_cons_hd. }
      { simpl.
        apply Vector.In_cons_tl.
        apply IHlen.
        rewrite Nat.add_comm.
        apply Hr. }
    }
  }
Qed.

Lemma In_destruct : forall n A (a h:A) (v : Vector.t A n),
  Vector.In a (h :: v) -> a = h \/ Vector.In a v.
Proof.
  intros.
  inversion H.
  { left. trivial. }
  { apply Eqdep.EqdepTheory.inj_pair2 in H3.
    subst.
    right.
    assumption. }
Qed.

Theorem In_seq:
  forall n start len : nat, Vector.In n (vseq start len) <-> start <= n < start + len.
Proof.
  intros.
  rewrite In_list.
  apply in_seq.
Qed.

Theorem InV_correct A n a (vec : Vector.t A n) : InV a vec <-> Vector.In a vec.
Proof.
  split.
  { induction vec.
    { intro H. inversion H. }
    { intros. simpl in H. destruct H.
      { subst. apply Vector.In_cons_hd. }
      { apply Vector.In_cons_tl. apply IHvec. assumption. }
    }
  }
  { intros.
    induction H; cbn; [left | right]; trivial. }
Qed.
