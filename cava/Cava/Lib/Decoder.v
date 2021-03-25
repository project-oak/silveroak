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

Section WithCava.
  Context `{semantics:Cava}.

  (* Fork a wire into N branches. *)
  Definition forkN {t : SignalType} (n : nat) (v : signal t)
    : cava (signal (Vec t n)) :=
    packV (Vector.const v n).

  Definition map2VC {n a b c}
    (f: a -> signal b -> cava (signal c))
    (v1: Vector.t a n)
    : signal (Vec b n)
    -> cava (signal (Vec c n))
    :=  unpackV
    >=> Vector.map2 (fun f v => f v) (Vector.map f v1)
    >=> mapT_vector id
    >=> packV.


  (* A decoder from binary to one-hot. Both are big endian *)
  Definition decoder {n : nat}
    : signal (Vec Bit n) -> cava (signal (Vec Bit (2^n)))
    := forkN (2^n) >=> map2VC (vecConstEq n) (Vector.vseq 0 (2^n)).

  Definition encoder {n: nat} : signal (Vec Bit (2^n)) -> cava (signal (Vec Bit n))
    := map2VC
         (fun k hot_sig =>
           packV (Vector.map
             (fun bit : bool => if bit then hot_sig else zero)
             (N2Bv_sized n (N.of_nat k))))
         (Vector.vseq 0 (2^n))
    >=> tree (Vec.map2 or2).

End WithCava.
