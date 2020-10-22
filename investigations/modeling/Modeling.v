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

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.

(* The usual sequential semantics we use with Lava style cicuits operates
   over lists or stream. This is an experiment to how an alternative approach
   works where signals are functions from a time index to a value. *)

(* An invertor of an input signal at time t is the negation of the input value.
*)
Definition inv (i : nat -> bool) : nat -> bool :=
  fun t => negb (i t).

(* A sequential nand2 gate performs a pointwise AND over the two inputs
   stream. *)
Definition and2 (a : nat -> bool) (b : nat -> bool) : nat -> bool :=
  fun t => a t &&  b t.

(* A NAND gate is simply the composition of inv and and2. *)
Definition nandGate a b := inv (and2 a b).

(* A delay models a register state element that delays its input by one
   tick and has the default value false at t=0. *)
Definition delay (i : nat -> bool) : nat -> bool  :=
  fun t => match t with
           | O => false
           | S t' => i t'
        end.

(* Some sample input streams. *)
Definition s1 t := nth t [true; true;  false; true;  true; false] false.
Definition s2 t := nth t [true; false; false; false; true; true]  false.

Compute map (delay s1) (seq 0 7).

Compute map (nandGate s1 s2) (seq 0 7).

Lemma nand_correct: forall (t : nat)
                           (a b : nat -> bool),
                           nandGate a b t = negb (a t && b t).
Proof.
  intros.
  auto.
Qed.


(* A pipelined NAND gate that has a register at the output of the AND2 gate.*)
Definition pipelinedNAND a b := inv (delay (and2 a b)).

(* The expected behaviour of the pipelined NAND gate. *)
Definition pipelinedNAND_spec a b t :=
  match t with
  | O => true
  | S n' => negb ((a n') && (b n'))
  end.

Compute map (pipelinedNAND s1 s2) (seq 0 7).
Compute map (pipelinedNAND_spec s1 s2) (seq 0 7).

(* A proof that the implemented pipelined NAND has the same behaviour as
   the spec. *)
Lemma pipelinedNAND_correct: forall (t : nat)
                            (a b : nat -> bool), 
                            pipelinedNAND a b t = pipelinedNAND_spec a b t.
Proof.
  intros.
  unfold pipelinedNAND.
  unfold pipelinedNAND_spec.
  unfold delay. unfold and2.
  unfold inv. destruct t.
  - simpl. reflexivity.
  - reflexivity.
Qed.

(* Next step: a circuit with a loop e.g. a counter. *)

                             