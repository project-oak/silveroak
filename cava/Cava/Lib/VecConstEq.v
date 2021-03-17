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

Require Import Coq.Vectors.Vector.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monads.
Import VectorNotations.
Import MonadNotation.
Local Open Scope vector_scope.
Local Open Scope monad_scope.
Local Open Scope N_scope.

Require Import Cava.Cava.
Require Import Cava.Lib.Vec.


Section WithCava.
  Context {signal} `{Cava signal}.

  (* Check if [inp] is bit-equal to the first [n] bits of [v] *)
  (* TODO(atondwal): use [Fin] to disallow numbers larger than [2^n]. c.f. [ex5] *)
  Definition vecConstEq {n v: nat}
                        (inp: signal (Vec Bit n)) :
                        cava (signal Bit) :=
    const <- bitvec_literal (N2Bv_sized n (N.of_nat v)) ;;
    eq_results <- Vec.map2 (fun '(a, b) => xnor2 (a, b)) (inp, const) ;;
    match n with
    | 0%nat => ret one
    | S _ => tree and2 eq_results
    end.

  Definition vecConstEq_combinator (n v: nat):= Comb (@vecConstEq n v).

End WithCava.


Example ex1 : simulate (vecConstEq_combinator 8 42) [N2Bv_sized 8 42] = [true].
Proof. trivial. Qed.

Example ex2 : simulate (vecConstEq_combinator 8 43) [N2Bv_sized 8 42] = [false].
Proof. trivial. Qed.

Example ex3 : simulate (vecConstEq_combinator 1 1) [N2Bv_sized 1 1] = [true].
Proof. trivial. Qed.

Example ex4 : simulate (vecConstEq_combinator 1 1) [N2Bv_sized 1 0] = [false].
Proof. trivial. Qed.

Example ex5 : simulate (vecConstEq_combinator 1 3) [N2Bv_sized 1 1] = [true].
Proof. trivial. Qed.
