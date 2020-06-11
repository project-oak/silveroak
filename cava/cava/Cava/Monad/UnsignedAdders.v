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

Require Import ExtLib.Structures.Monads.

Require Import Nat Arith Lia.

Require Import Cava.Cava.
From Cava Require Import Kind.
Require Import Cava.Monad.CavaMonad.

(******************************************************************************)
(* An adder with two inputs of the same size and no bit-growth                *)
(******************************************************************************)

Lemma n_le_max_n_n : forall n, n <= S(max n n).
Proof.
  intros. lia.
Qed.

Definition addN {m bit} `{Cava m bit} {n}
                (a: vec Bit n) (b: vec Bit n) : m (vec Bit n) :=
  s <- unsignedAdd a b ;;
  ret (slice 0 n s (n_le_max_n_n n)).

(******************************************************************************)
(* A three input adder.                                                       *)
(******************************************************************************)

Definition adder_3input {m bit} `{Cava m bit}
                        {aSize bSize cSize}
                        (a : vec Bit aSize)
                        (b : vec Bit bSize)
                        (c : vec Bit cSize) :
                        m (vec Bit (1 + max (1 + max aSize bSize) cSize))
                        :=
  a_plus_b <- unsignedAdd a b ;;
  sum <- unsignedAdd a_plus_b c ;;
  ret sum.
