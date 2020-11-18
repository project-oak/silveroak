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

Require Import Init.Nat Arith.Arith micromega.Lia.

Require Import Cava.Cava.
From Cava Require Import Kind.
Require Import Cava.Monad.CavaMonad.

Section WithCava.
  Context {signal} `{Cava signal} `{Monad cava}.

  (****************************************************************************)
  (* An adder with two inputs of the same size and no bit-growth              *)
  (****************************************************************************)

  Lemma n_le_n_plus_1 : forall n, 0 + n <= 1 + n.
  Proof. auto. Defined.

  Lemma max_n_n : forall n, max n n = n.
  Proof.
    intros.
    induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Defined.

  Definition deMax {n} (v: signal (Vec Bit (1 + max n n))) :
                       signal (Vec Bit (1+n)).
  Proof.
    rewrite max_n_n in v.
    apply v.
  Defined.

  Definition addN {n: nat}
                  (a b: signal (Vec Bit n))
                  : cava (signal (Vec Bit n)) :=
    s <- unsignedAdd a b ;;
    ret (slice 0 n (deMax s) (n_le_n_plus_1 _)).

  (****************************************************************************)
  (* A three input adder.                                                     *)
  (****************************************************************************)

  Definition adder_3input {aSize bSize cSize}
                          (a : signal (Vec Bit aSize))
                          (b : signal (Vec Bit bSize))
                          (c : signal (Vec Bit cSize)) :
                          cava (signal (Vec Bit (1 + max (1 + max aSize bSize) cSize)))
                          :=
    a_plus_b <- unsignedAdd a b ;;
    sum <- unsignedAdd a_plus_b c ;;
    ret sum.

 End WithCava.