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

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Lists.List.
Require Import Program.Basics.
Local Open Scope program_scope.

(*** Various experiments for representing synchronous gate-level
     circuits in Coq in a Lava-style.
***)

(* A deep embeding with a data structure that represents Cava circuit
   expressions.
*)

Inductive signal : Type :=
  | Bit : signal
  | Tuple2 : forall A B, A -> B -> signal.


Inductive cava : signal -> Set :=
  | Inv : cava Bit -> cava Bit
  | And2 : cava Bit * cava Bit -> cava Bit
  | Or2 : cava Bit * cava Bit -> cava Bit
  | Xor2 : cava Bit * cava Bit -> cava Bit
  | Xorcy : cava Bit * cava Bit -> cava Bit
  | Muxcy : (cava Bit * (cava Bit * cava Bit)) -> cava Bit
  | Delay : cava Bit -> cava Bit
  (*
  | Fork2 : forall (A : signal), cava A -> cava (Tuple2 A A)
  | Par2 : forall (A : signal) (B : signal), cava A -> cava B -> cava (Tuple2 A 
  *)
  | Signal : string -> cava Bit
  | Output : string -> cava Bit -> cava Bit.

(* A list-based semantics for gate level elements. We could also
   use streams.
*)

Definition inv_comb (x : bool) : bool :=
  match x with
    | true => false
    | false => true
  end.

Definition inv (x : list bool) : list bool := map inv_comb x.

Definition and2_comb (xy : bool*bool) : bool := fst xy && snd xy.
Fixpoint and2 (x y : list bool) : list bool := map and2_comb (combine x y).

Definition or2_comb (xy : bool*bool) : bool := fst xy || snd xy.
Fixpoint or2 (x y : list bool) : list bool := map or2_comb (combine x y).

Definition xor2_comb (xy : bool*bool) : bool := xorb (fst xy) (snd xy).
Fixpoint xor2 (x y : list bool) : list bool := map or2_comb (combine x y).

Definition xorcy := xor2.

Definition muxcy_comb (cidis : bool*bool*bool) : bool
  := let '(ci, di, s) := cidis
     in if s then
          di
        else
          ci.
Fixpoint muxcy (ci di s : list bool) : list bool
  := map muxcy_comb (combine (combine ci di) s).

Fixpoint delay (x : list bool) : list bool := false :: x.

Definition delayInit1 := Delay ∘ Inv.
