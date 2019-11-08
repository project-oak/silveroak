(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
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

Require Import AltCava.
From Coq Require Import Ascii String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.


Definition reorg1Fn (T : Type) 
                    (cinab : @signal T ‹Bit, ‹Bit, Bit››) : @signal T ‹‹Bit, Bit›, ‹Bit, Bit››
  := match cinab with
       (cin, (a, b)) =>  ((cin, a), (a, b))
     end.

Definition reorg1 : cava ‹Bit, ‹Bit, Bit›› ‹‹Bit, Bit›, ‹Bit, Bit››
           := Reshape reorg1Fn.

Definition reorg2Fn (T : Type)
                    (cinaps : @signal T ‹‹Bit, Bit›, Bit›) :
                     @signal T ‹‹Bit, Bit›, ‹Bit, ‹Bit, Bit›››
  := match cinaps with
       ((cin, a), ps) => ((cin, ps), (ps, (a, cin)))
     end.

Definition reorg2 := Reshape reorg2Fn.

Definition oneBitAdder : cava ‹Bit, ‹Bit, Bit›› ‹Bit, Bit›
  := reorg1  ⟼ second xor2  ⟼ reorg2  ⟼ (xorcy ‖ Muxcy).

Lemma oneBitAdder_combinational :
  forall (cin a b : bool), cavaCombinational oneBitAdder (cin, (a, b))
    = (xorb cin (xorb a b), orb a (cin && (xorb a b))).
  intros.
  unfold oneBitAdder.
  simpl.


Definition oneBitAdder_top
  := (Input "cin" ‖ (Input "a" ‖ Input "b"))  ⟼
     oneBitAdder  ⟼
     ((Output "sum") ‖ (Output "cout")).
