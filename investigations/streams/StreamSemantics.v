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
Import ListNotations.
From Coq Require Import Lists.Streams.

(* An infinite list of 0/false. *)
CoFixpoint zeroes : Stream bool := Cons false zeroes.

(* An infinite list of 1/true. *)
CoFixpoint ones : Stream bool := Cons true ones.

(* Semantics for an invertor. *)
CoFixpoint inv (i : Stream bool) : Stream bool :=
  match i with
  | Cons h t => Cons (negb h) (inv t)
  end.

(* Define a function to consume a finite amount of a stream. *)
Fixpoint takeStream {A} (s : Stream A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: takeStream t n'
      end
  end.

(* Apply inv to an infinite stream of ones, evalate first 10 ticks. *)
 Compute takeStream (inv ones) 10. 

 (* Semantics for an AND gate. *)
CoFixpoint and2 (i : Stream bool * Stream bool) : Stream bool :=
  match i with
  | (Cons h1 t1, Cons h2 t2) => Cons (andb h1 h2) (and2 (t1, t2))
  end.

 (* Semantics for an OR gate. *)
CoFixpoint or2 (i : Stream bool * Stream bool) : Stream bool :=
  match i with
  | (Cons h1 t1, Cons h2 t2) => Cons (orb h1 h2) (or2 (t1, t2))
  end.

(* alt0 is an infinite stream of alternating 0/1 values, starting with 0 *)
(* alt1 is an infinite stream of alternating 0/1 values, starting with 1 *)
CoFixpoint alt0 : Stream bool := Cons false alt1
with alt1 : Stream bool := Cons true alt0.

(* Duplicate each element of the stream. *)
CoFixpoint stretch2 (i : Stream bool) : Stream bool :=
  match i with
  | Cons h t => Cons h (Cons h (stretch2 t))
  end.

(* alt0_2 is like alt0 but at half the frequency. *)
Definition alt0_2 :=  stretch2 alt0.

(* Make sure we get the expected output for an AND2 gate:
  [false; false; false; true]
  : list bool
*)
Compute takeStream (and2 (alt0, alt0_2)) 4.

(* Make sure we get the expected output for an OR2 gate:
  = [false; true; true; true]
  : list bool
*)
Compute takeStream (or2 (alt0, alt0_2)) 4.

(* Model a register bit (flip-flop) with a unit delay element. *)
Definition delayBit (i : Stream bool) : Stream bool :=
  match i with
  | Cons h t => Cons false i
  end.

(* Is it possible to define loopNat i.e. a loop combinator specialized
   to a nat type on the feedback path?
*)
CoFixpoint loopNat {A B} (f : Stream A * Stream nat -> Stream B * Stream nat)
                         (i : Stream A)
                         : Stream B.