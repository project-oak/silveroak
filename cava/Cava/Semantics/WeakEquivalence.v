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

(*
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
Proof.
  intros [Rab [Hab1 [Hab2 [Hab3 Hab4]]]].
  intros [Rcd [Hcd1 [Hcd2 [Hcd3 Hcd4]]]].
  exists (fun i s1 s2 =>
       (m < i -> Rab (i - m) (fst s1) (fst s2))
       /\ (i <= m -> Rcd i (snd s1) (snd s2))).
  cbn [value circuit_state].
  ssplit; intros; destruct_products; cbn [fst snd step] in *;
    repeat
      lazymatch goal with
      | H : ?x + ?y <= ?y |- _ =>
        destruct x; [ | lia ]; autorewrite with natsimpl in *
      | H : ?x < 1 |- _ =>
        destruct x; [ clear H | lia ]; autorewrite with natsimpl in *
      | H1 : ?y < ?x -> _, H2 : ?x <= ?y -> _ |- _ =>
        destr (x <=? y); [ specialize (H2 ltac:(lia)); clear H1
                         | specialize (H1 ltac:(lia)); clear H2 ]
      | H : Rab 1 ?s1 ?s2 |- context [step a ?s1] => erewrite Hab3 by eassumption
      | H1 : ?x <= ?y, H2 : ?y < S ?x |- _ =>
        assert (x = y) by lia; subst; clear H1
      | _ => first
              [ progress (ssplit; intros)
              | erewrite Hab2 by lia
              | apply Hcd2; lia
              | apply Hab4; [ lia | solve [auto] ]
              | solve [auto]
              | lia
              | rewrite Nat.sub_succ_l in * by lia
              | progress autorewrite with natsimpl in * ]
      end.
Qed.

Lemma cequivn_delays {t} (r1 r2 : value t) : cequivn 1 (DelayInit r1) (DelayInit r2).
Proof.
  exists (fun i s1 s2 => i <= 1 /\ s1 = s2). cbn [value step circuit_state].
  ssplit; intros; logical_simplify; subst; ssplit; try reflexivity; lia.
Qed.

Lemma cequivn_comb {i o} (f g : value i -> cava (value o)) :
  (forall x, f x = g x) -> cequivn 0 (Comb f) (Comb g).
Proof.
  intro Hfg. exists (fun i s1 s2 => i = 0). cbn [value step circuit_state].
  ssplit; intros; logical_simplify; subst; ssplit;
    repeat lazymatch goal with x : unit |- _ => destruct x end;
    rewrite ?Hfg; try reflexivity; lia.
Qed.

Instance Symmetric_cequivn {i o} n : Symmetric (@cequivn i o n) | 10.
Proof.
  intros x y [R ?]. logical_simplify. exists (fun i sx sy => R i sy sx).
  ssplit; intros; auto; symmetry; auto.
Qed.

(* Restriction that states a circuit is cequivn-equivalent to itself for some n;
   that is, the number of delays betweeen the inputs and each of the outputs is
   the same. This will not include most circuits with loops. *)
Definition uniformly_timed {i o} n (c : Circuit i o) : Prop := cequivn n c c.

Definition wequiv {i o} (c1 c2 : Circuit i o) : Prop :=
  (* either both circuits are non-uniformly timed *)
  ((forall n, ~ uniformly_timed n c1)
   /\ (forall n, ~ uniformly_timed n c2))
  (* ...or both are uniformly timed with the same timing, and they are
     cequivn-equivalent with respect to that timing *)
  \/ (exists n, uniformly_timed n c1
          /\ uniformly_timed n c2
          /\ cequivn n c1 c2).

Instance Reflexive_wequiv {i o} : Reflexive (@wequiv i o) | 10.
Proof.
  repeat intro. cbv [wequiv].
  (* here's where we need to *decide* if c is uniformly timed or not *)

  (* thing that returns value nat i -> value nat o
     Compose f g := fun is => match time f is with
                              | Some ns => utime g ns

   *)
Qed.
Instance Symmetric_wequiv {i o} : Symmetric (@wequiv i o) | 10.
Proof.
  repeat intro. cbv [wequiv] in *. logical_simplify.
  symmetry; auto.
Qed.
Instance Transitive_wequiv {i o} : Transitive (@wequiv i o) | 10.
Proof.
  repeat intro. cbv [wequiv] in *. logical_simplify.
  (* This relation is not transitive; a non-uniform y could make both preconditions vacuous *)
  symmetry; auto.
Qed.

Print Circuit.

(* Circuits with uniform timing characteristics; all outputs have the same
   number of delays between them and the circuit inputs *)
Inductive UCircuit `{semantics:Cava} : nat -> type -> type -> Type :=
| Comb : forall {i o : type}, (value i -> cava (value o)) -> UCircuit 0 i o
| Compose : forall {i t o n m}, UCircuit n i t -> UCircuit m t o -> UCircuit (n + m) i o
| Par : forall {i1 i2 o1 o2 n}, UCircuit n i1 o1 -> UCircuit n i2 o2 -> UCircuit n (i1 * i2) (o1 * o2)
| LoopInitCE : forall {i o s n}, @value combType s -> UCircuit n (i * s) (o * s) -> UCircuit 0 (i * Bit) o
| DelayInitCE




(* Circuit equivalence relation that declares the circuits produce equivalent
   outputs for equivalent inputs after a certain number of delays *)
Definition wequiv {i o} (c1 c2 : Circuit i o) : Prop :=
  exists n, cequivn n c1 c2.

Global Instance Transitive_wequiv {i o : type} : Transitive (@wequiv i o) | 10.
Admitted.

Global Instance Symmetric_wequiv {i o : type} : Symmetric (@wequiv i o) | 10.
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
  cbv [wequiv]. exists 1. exists (fun i s1 s2 => i <= 1 /\ s1 = s2).
  cbn [value step circuit_state].
  ssplit; intros; logical_simplify; subst; ssplit;
    try reflexivity; lia.
Qed.
*)
