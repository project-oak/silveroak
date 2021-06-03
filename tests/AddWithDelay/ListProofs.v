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
Require Import Tests.AddWithDelay.AddWithDelay.
Import Circuit.Notations.

Definition bvadd {n} (a b : Signal.combType (Vec Bit n)) : Signal.combType (Vec Bit n) :=
  N2Bv_sized n (Bv2N a + Bv2N b).

Definition bvzero {n} : Signal.combType (Vec Bit n) := N2Bv_sized n 0.

Definition addWithDelaySpecF
           (input : nat -> Signal.combType (Vec Bit 8)) : nat -> Signal.combType (Vec Bit 8) :=
  fix out (t : nat) :=
    match t with
    | 0 => bvzero (* first round is just a delay *)
    | 1 =>
      (* second round is first input (because initial feedback = 0) *)
      input 0
    | S (S t') =>
      (* if t > 2, out(t) = in(t-1) + out(t-2) *)
      bvadd (input (S t')) (out t')
    end.

Lemma addNCorrect n (a b : combType (Vec Bit n)) :
  addN (a, b) = bvadd a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : simpl_ident.

Lemma addWithDelayStepCorrect :
  forall (i s : Bvector 8) (st : circuit_state _),
    step (Comb addN >==> Delay >==> Comb fork2) st (i, s)
    = (tt, (tt, bvadd i s), tt,
       (snd (snd (fst st)), snd (snd (fst st)))).
Proof.
  intros. cbv [mcompose step Delay].
  repeat first [ destruct_pair_let | progress simpl_ident ].
  reflexivity.
Qed.

Lemma Bv2N_bvzero n : Bv2N (@bvzero n) = 0%N.
Proof.
  cbv [bvzero N2Bv_sized Bvect_false].
  induction n; intros; [ reflexivity | ].
  rewrite const_cons. cbn [Bv2N].
  rewrite IHn. reflexivity.
Qed.

Lemma bvadd_bvzero_l {n} (x : Bvector n) : bvadd x bvzero = x.
Proof.
  cbv [bvadd]. rewrite Bv2N_bvzero.
  rewrite N.add_0_r, N2Bv_sized_Bv2N.
  reflexivity.
Qed.

Lemma addWithDelayCorrect (i : list (Bvector 8)) :
  simulate addWithDelay i = map (fun t => addWithDelaySpecF (fun n => nth n i bvzero) t)
                                 (seq 0 (length i)).
Proof.
  intros; cbv [addWithDelay]. autorewrite with push_simulate.
  cbn [step Delay]. simpl_ident.
  eapply fold_left_accumulate_invariant_seq
      with (I := fun t (st : unit * (unit * Vector.t bool 8) * unit * Vector.t bool 8) acc =>
                 st = (tt, (tt, addWithDelaySpecF (fun n => nth n i bvzero) t), tt,
                       match t with
                       | 0 => bvzero
                       | S t => addWithDelaySpecF (fun n => nth n i bvzero) t
                       end)
                 /\ acc = map (fun t => addWithDelaySpecF
                                      (fun n => nth n i bvzero) t)
                             (seq 0 t)).
  { (* invariant is satisfied at start *)
    ssplit; reflexivity. }
  { (* invariant holds through loop *)
    cbv zeta; intros; logical_simplify. subst.
    cbn [step mcompose Delay fst snd].
    repeat first [ destruct_pair_let | progress simpl_ident ].
    destruct t.
    { destruct i; cbn [length] in *; [length_hammer | ].
      ssplit; try reflexivity; [ ].
      cbn [nth]. rewrite bvadd_bvzero_l.
      reflexivity. }
    { (* change default to bvzero *)
      match goal with |- context [nth _ _ ?x] =>
                      is_var x;
                      rewrite nth_inbounds_change_default
                        with (d1:=x) (d2:=bvzero)
                        by length_hammer
      end.
      ssplit; try reflexivity; [ ].
      autorewrite with pull_snoc natsimpl. reflexivity. } }
  { (* invariant implies postcondition *)
    intros; logical_simplify; subst.
    reflexivity. }
Qed.
