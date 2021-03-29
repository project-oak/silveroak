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

Require Import Cava.Cava.
Require Import Cava.Lib.VecConstEq.
Require Import Coq.Arith.PeanoNat.
Require Import Cava.Util.Vector.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Functor.

Import FunctorNotation.

Section WithCava.
  Context `{semantics:Cava}.

  (* A decoder from binary to one-hot. Both are big endian *)
  Definition decoder {n : nat} (bv : signal (Vec Bit n))
    := Vec.map_literal
        (fun f => f bv)
        (Vector.map (vecConstEq n) (Vector.vseq 0 (2^n))).

  Definition encoder {n: nat}
    (hot : signal (Vec Bit (2^n)))
    : cava (signal (Vec Bit n))
    :=         (* Go from Vector of Bvector to Vec of Vec *)
    consts <- Vec.map_literal ret
      (mapT_vector
        (@Vec.bitvec_literal signal semantics  _)
        (* build a Vector.t of constant bitvecs 0...2^n *)
        (Vector.map (fun k => N2Bv_sized n (N.of_nat k))
                    (Vector.vseq 0 (2^n)))) ;;
    Vec.map2
      (fun '(k, hot_sig) => mux2 hot_sig (defaultSignal, k))
      (consts, hot)
    >>= tree (Vec.map2 or2).

End WithCava.
