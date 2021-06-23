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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Semantics.Loopless.
Require Import Cava.Semantics.LooplessProperties.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Import Circuit.Notations.

(* Circuit equivalence relation that stipulates an equal output after n timesteps *)
Definition cequivn {i o} (n : nat) (c1 c2 : Circuit i o) : Prop :=
  (* there exists some relation between the circuit states and a counter... *)
  exists (R : nat -> value (circuit_state c1) -> value (circuit_state c2) -> Prop),
    (* ...and after an equal input, R holds with a full counter (if n=0, then
       the output is also equal) *)
    (forall s1 s2 v, R n (fst (step c1 s1 v)) (fst (step c2 s2 v)))
    (* ...and if n happens to be 0, then the outputs are equal on equal input *)
    /\ (n = 0 -> forall s1 s2 v, snd (step c1 s1 v) = snd (step c2 s2 v))
    (* ...and if the relation holds for a one counter, outputs are equal
       regardless of input *)
    /\ (forall s1 s2 v1 v2, R 1 s1 s2 -> snd (step c1 s1 v1) = snd (step c2 s2 v2))
    (* ...and if the relation holds for a nonzero counter, it holds on new
       states with a decremented counter regardless of input *)
    /\ (forall m s1 s2 v1 v2,
          0 < m ->
          R (S m) s1 s2 ->
          R m (fst (step c1 s1 v1)) (fst (step c2 s2 v2))).


Lemma cequivn_compose {i t o} n m (a b : Circuit i t) (c d : Circuit t o) :
  cequivn n a b -> cequivn m c d -> cequivn (n + m) (a >==> c) (b >==> d).
Admitted.

(* count the number of delays on the critical path of a circuit *)
Fixpoint cpath {i o} (c : Circuit i o) : nat :=
  match c with
  | Comb _ => 0
  | First f => cpath f
  | Second f => cpath f
  | Compose f g => cpath f + cpath g
  | DelayInit _=> 1
  | LoopInitCE _ body => cpath body
  end.

Definition cequivn_reflexive {i o} (c : Circuit i o) :
  is_loop_free c = true -> cequivn (cpath c) c c.
Proof.
  induction c; cbn [cpath is_loop_free].
  { exists (fun i s1 s2 => i = 0 /\ s1 = s2).
    ssplit; cbn [value step circuit_state]; intros; subst.
    all:logical_simplify.
    all:ssplit; try reflexivity.
    all:discriminate. }
  { rewrite Bool.andb_true_iff; intros; logical_simplify.
    apply cequivn_compose; auto. }
  { admit. (* applies across First *) }
  { admit. (* applies across Second *) }
  { discriminate. }
  { intros. exists (fun i s1 s2 => i <= 1 /\ s1 = s2).
    cbn [value step circuit_state].
    ssplit; intros; logical_simplify; subst; ssplit;
      try reflexivity; try lia. }
Admitted.

(* Circuit equivalence relation that declares the circuits have equal critical
   paths and, if both are loop-free, then they produce equivalent outputs for
   equivalent inputs (delayed by the critical path number) *)
Definition wequiv {i o} (c1 c2 : Circuit i o) : Prop :=
  cpath c1 = cpath c2
  /\ (is_loop_free c1 = true ->
     is_loop_free c2 = true ->
     cequivn (cpath c1) c1 c2).

Global Instance Equivalence_wequiv: forall {i o : type}, Equivalence (@wequiv i o) | 10.
Admitted.

Global Instance Proper_Second {i o t : type} :
  Proper (@wequiv i o ==> @wequiv (t * i) (t * o)) Second.
Admitted.

Global Instance Proper_First {i o t : type} :
  Proper (@wequiv i o ==> @wequiv (i * t) (o * t)) First.
Admitted.

Global Instance Proper_Compose {i o t : type} :
  Proper (@wequiv i t ==> @wequiv t o ==> wequiv) Compose.
Admitted.

Lemma wequiv_delays {t} (r1 r2 : value t) : wequiv (DelayInit r1) (DelayInit r2).
Proof.
  cbv [wequiv]. cbn [cpath is_loop_free]. ssplit; [ reflexivity | intros ].
  intros. exists (fun i s1 s2 => i <= 1 /\ s1 = s2).
  cbn [value step circuit_state].
  ssplit; intros; logical_simplify; subst; ssplit;
    try reflexivity; try lia.
Qed.
