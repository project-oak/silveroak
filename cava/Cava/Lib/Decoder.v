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

Section WithCava.
  Context `{semantics:Cava}.

  (* A decoder from binary to one-hot. Both are big endian *)
  Definition decoder {n : nat} (bv : signal (Vec Bit n))
    : cava (signal (Vec Bit (2^n)))
    := Vec.map_literal
        (fun (f: signal (Vec Bit n) -> cava (signal Bit)) => f bv)
        (Vector.unfold 0 (fun (k:nat) => (vecConstEq n k, S k))).


  Definition encoder {n: nat} (one_hot : signal (Vec Bit (2^n)))
    : cava (signal (Vec Bit n))
    := Vec.map_acc_l
         0
         (fun k hot_sig => packV (Vector.map
             (fun bit : bool => if bit then hot_sig else zero)
             (N2Bv_sized n (N.of_nat k)))
           >>= fun v => ret (v, S k))
         (one_hot)
    >>= fun '(v,c) => ret v
    >>= tree (Vec.map2 or2).

End WithCava.
