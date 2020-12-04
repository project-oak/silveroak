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

From Coq Require Import Strings.Ascii Strings.String.
From Coq Require Import NArith.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.Monad.CavaMonad.

From Coq Require Vector.
From Coq Require Import Bool.Bvector.

Section WithCava.
  Context {signal} `{Cava signal} `{Monad cava}.

  Definition delayByte (i : signal (Vec Bit 8))
                       : cava (signal (Vec Bit 8)) :=
  delay i.

End WithCava.

Definition b0 := N2Bv_sized 8 0.
Definition b14 := N2Bv_sized 8 14.
Definition b7 := N2Bv_sized 8 7.
Definition b250 := N2Bv_sized 8 250.

Local Open Scope list_scope.

Example delay_ex1: sequential (delayByte [b14; b7; b250]) = [b0; b14; b7; b250].
Proof. reflexivity. Qed.

Lemma delayByteBehaviour: forall (i : list (Bvector 8)),
                          sequential (delayByte i) =  b0 :: i.
Proof.
  reflexivity.
Qed.

Definition delayByte_Interface
  := sequentialInterface "delayByte"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)]
     [].

Definition delayByte_Netlist := makeNetlist delayByte_Interface delayByte.

Definition delayByte_tb
  := testBench "delayByte_tb" delayByte_Interface
      [b14; b7; b250]  [b0; b14; b7].
