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

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Lib.CircuitTransforms.
Require Import Cava.Lib.CircuitTransformsProperties.
Require Import Cava.Lib.Retiming.
Require Import Cava.Util.Tactics.
Import ListNotations Circuit.Notations.

Lemma retimed_cequiv_iff {i o} (c1 c2 : Circuit i o) :
  retimed 0 c1 c2 <-> cequiv c1 c2.
Proof.
  split.
  { intros [R ?]. logical_simplify.
    exists (R 0).
    ssplit; [ assumption | ]. intros.
    specialize
      (HR 0 _ _ (ltac:(eassumption)) (ltac:(eassumption))
          (ltac:(eassumption)) (ltac:(lia))).
    cbn iota in *. rewrite (proj2 HR).
    logical_simplify. ssplit; eauto. }
  { intros [R [? HR]]. exists (fun _ => R).
    ssplit; [ assumption | ]. intros.
    destruct m; [ | lia ].
    ssplit; intros; subst.
    2:{
    specialize
      (HR _ _ (ltac:(eassumption)) (ltac:(eassumption))).
    logical_simplify. ssplit; eauto.
    rewrite (proj2 HR). logical_simplify. ssplit; eauto. }
Qed.

(*
Lemma retimed_sum {i o} (n m: nat) (c1 c2 c3 : Circuit i o) :
  retimed (n+m) c1 c2 -> retimed n c1 c3 -> retimed m c2 c3.
Proof.
  intros [R12 [? H12]]. intros [R13 [? H13]].
  exists (fun i (st2 : circuit_state c2) (st3 : circuit_state c3) =>
       exists st1, R12 i st1 st2
              /\ R13 (Nat.modulo (i*m) n) st1 st3).
  ssplit.
  { exists (reset_state c1). ssplit; eauto.
Qed.
*)

(*
Lemma retimed_delays1_l_iff {i o} (n : nat) (c1 c2 : Circuit (ivalue i) o) :
  retimed 1 c1 c2
  <-> (exists resetvals : ivalue i,
        cequiv c1 (delays i resetvals >==> c2)).
Admitted.
 *)

(*
the second part matches every m cycles
the first part matches every n cycles

assume m=2, n=3

0:reset
2:second part matches
3:first part matches
4:second part matches
6:first part matches
??????
ahhhh, the second part matches only m cycles *after its input matches*



if we are i steps away from matching...

if i <= m,
 the second part is i steps away from matching
else
 second part unclear but does have an R


 *)

Lemma retimed_compose A B C n m (c1 c2 : Circuit A B) (c3 c4 : Circuit B C) :
  retimed n c1 c2 -> retimed m c3 c4 -> retimed (n+m) (c1 >==> c3) (c2 >==> c4).
Proof.
  intros [R12 [? H12]] [R34 [? H34]].
  exists (fun i st1 st2 =>
       R12 (i - m) (fst st1) (fst st2)
       /\ R34 i (snd st1) (snd st2)).
  cbn [reset_state fst snd].
  ssplit;
    [ autorewrite with natsimpl;
      solve [eauto] | | ].
  { 
  cbn [circuit_state]. intros.
  destruct_products; cbn [fst snd] in *.
  logical_simplify. destruct_one_match.
  { autorewrite with natsimpl in *.
    cbn [step]. repeat (destruct_pair_let; cbn [fst snd]).
    specialize (H34 0 _ _ (ltac:(eassumption)) (ltac:(lia))
                    (ltac:(eassumption))).
    cbn iota in H34. destruct H34 as [H34 ?].
    rewrite H34 in *.
  { 
Qed.

Lemma retimed_succ {i o} n (c1 c2 : Circuit (ivalue i) o) :
  retimed (S n) c1 c2 ->
  exists resetvals, retimed n c1 (delays i resetvals >==> c2).
Proof.
Qed.

Lemma retimed_ndelays_l_iff {i o} (n : nat) (c1 c2 : Circuit (ivalue i) o) :
  retimed n c1 c2 <-> (exists resetvals : list (ivalue i),
                        length resetvals = n
                        /\ cequiv c1 (ndelays i resetvals >==> c2)).
Proof.
  split.
  { revert i o c1 c2; induction n; intros *.
    { rewrite retimed_cequiv_iff.
      intros. exists nil. cbn [ndelays fold_left].
      autorewrite with circuitsimpl.
      ssplit; eauto. }
    {
      (* retimed (S n) c1 c2 -> exists c3, retimed n c1 c3 /\ cequiv c3 (delays >==> c2) *)
      
      intros [R [? HR]]. logical_simplify.
    

    (*
      equivalence state relation should say that R 0 holds on the last?
    *)

    evar (r: list (ivalue (signal:=combType) i)).
    exists r. ssplit.
    2:{
      exists (fun (st1 : circuit_state c1)
           (st2 : circuit_state (ndelays i r) * circuit_state c2) =>
           R 0 st1 (snd st2)).
      
Qed.

