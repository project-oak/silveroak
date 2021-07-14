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

(* Change the reset state of a circuit *)
Fixpoint chreset {i o} (c : Circuit i o) : @value combType (circuit_state c) -> Circuit i o :=
  match c with
  | Comb f => fun _ => Comb f
  | Compose f g => fun r => Compose (chreset f (fst r)) (chreset g (snd r))
  | First f => fun r => First (chreset f r)
  | Second f => fun r => Second (chreset f r)
  | LoopInitCE _ body => fun r => LoopInitCE (snd r) (chreset body (fst r))
  | DelayInit _ => DelayInit
  end.

(* This is the identity function because it's always the case that circuit_state
   (chreset c r) = circuit_state c, but the explicit conversion helps with
   typechecking *)
Fixpoint from_chreset_state {i o} {c : Circuit i o} {struct c}
  : forall {r}, @value combType (circuit_state (chreset c r)) -> @value combType (circuit_state c) :=
  match c with
  | Comb f => fun _ x => x
  | Compose f g =>
    fun (r : value (circuit_state f) * value (circuit_state g))
      (x : value (circuit_state (chreset f (fst r))) * value (circuit_state (chreset g (snd r)))) =>
      (from_chreset_state (fst x), from_chreset_state (snd x))
  | First f => fun _ => from_chreset_state (c:=f)
  | Second f => fun _ => from_chreset_state (c:=f)
  | LoopInitCE _ body =>
    fun (r : value (circuit_state body) * value _)
      (x : value (circuit_state (chreset body (fst r))) * value _) =>
      (from_chreset_state (fst x), snd x)
  | DelayInit _ => fun r x => x
  end.

(* This is the identity function because it's always the case that circuit_state
   (chreset c r) = circuit_state c, but the explicit conversion helps with
   typechecking *)
Fixpoint to_chreset_state {i o} {c : Circuit i o} {struct c}
  : forall {r}, @value combType (circuit_state c) -> @value combType (circuit_state (chreset c r)) :=
  match c with
  | Comb f => fun _ x => x
  | Compose f g =>
    fun (r x : value (circuit_state f) * value (circuit_state g)) =>
      (to_chreset_state (fst x), to_chreset_state (snd x))
  | First f => fun _ => to_chreset_state (c:=f)
  | Second f => fun _ => to_chreset_state (c:=f)
  | LoopInitCE _ body =>
    fun (r x : value (circuit_state body) * value _) => (to_chreset_state (fst x), snd x)
  | DelayInit _ => fun r x => x
  end.

Lemma to_from_chreset_state {i o} (c : Circuit i o) r v:
  to_chreset_state (from_chreset_state (c:=c) (r:=r) v) = v.
Proof.
  induction c;
    cbn [to_chreset_state from_chreset_state value chreset circuit_state fst snd] in *.
  all: destruct_products; cbn [fst snd] in *; congruence || (f_equal; congruence).
Qed.

Lemma from_to_chreset_state {i o} (c : Circuit i o) r v:
  from_chreset_state (to_chreset_state (c:=c) (r:=r) v) = v.
Proof.
  induction c;
    cbn [to_chreset_state from_chreset_state value chreset circuit_state fst snd] in *.
  all: destruct_products; cbn [fst snd] in *; congruence || (f_equal; congruence).
Qed.

Lemma chreset_chreset {i o} (c : Circuit i o) r1 r2:
  chreset (chreset c r1) r2 = chreset c (from_chreset_state r2).
Proof.
  induction c; cbn [chreset circuit_state from_chreset_state value] in *;
    repeat match goal with H : _ |- _ => rewrite H end;
    reflexivity.
Qed.

Lemma chreset_noop {i o} (c : Circuit i o) : chreset c (reset_state c) = c.
Proof.
  induction c; cbn [chreset circuit_state reset_state value fst snd] in *;
    repeat match goal with H : _ |- _ => rewrite H end; reflexivity.
Qed.

Lemma chreset_reset {i o} (c : Circuit i o) r :
  reset_state (chreset c r) = to_chreset_state r.
Proof.
  induction c; cbn [chreset circuit_state reset_state value fst snd] in *;
    repeat match goal with H : _ |- _ => rewrite H end; reflexivity.
Qed.


Lemma step_chreset {i o} (c : Circuit i o) r s input :
  step (chreset c r) s input
  = (to_chreset_state (fst (step c (from_chreset_state s) input)),
     snd (step c (from_chreset_state s) input)).
Proof.
  induction c;
    cbn [circuit_state value chreset step fst snd
                       from_chreset_state to_chreset_state] in *;
    destruct_products; cbn [fst snd] in *;
      repeat match goal with H : _ |- _ => rewrite H end;
      reflexivity.
Qed.
