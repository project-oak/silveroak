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

Definition packBit {n} := @packV combType Combinational.CombinationalSemantics Bit n.

Example ex1 : decoder (N2Bv_sized 1 0) = packBit [true; false].
Proof. trivial. Qed.
Example ex2 : decoder (N2Bv_sized 1 1) = packBit [false; true].
Proof. trivial. Qed.

Example ex3 : decoder (N2Bv_sized 2 0) = packBit [true; false; false; false].
Proof. trivial. Qed.
Example ex4 : decoder (N2Bv_sized 2 1) = packBit [false; true; false; false].
Proof. trivial. Qed.
Example ex5 : decoder (N2Bv_sized 2 2) = packBit [false; false; true; false].
Proof. trivial. Qed.
Example ex6 : decoder (N2Bv_sized 2 3) = packBit [false; false; false; true].
Proof. trivial. Qed.

Definition encoderBit {n} := @encoder combType Combinational.CombinationalSemantics n.

Example ex7  : encoderBit (decoder (N2Bv_sized 2 0)) = (N2Bv_sized 2 0).
Proof. trivial. Qed.
Example ex8  : encoderBit (decoder (N2Bv_sized 2 1)) = (N2Bv_sized 2 1).
Proof. trivial. Qed.
Example ex9  : encoderBit (decoder (N2Bv_sized 2 2)) = (N2Bv_sized 2 2).
Proof. trivial. Qed.
Example ex10 : encoderBit (decoder (N2Bv_sized 2 3)) = (N2Bv_sized 2 3).
Proof. trivial. Qed.

Definition N2hotv {n} k : Bvector n := unfold_ix tt (fun ix tt => (Nat.eqb k ix, tt)).

Theorem dec_correct : forall n k, k < 2^n -> decoder (N2Bv_sized n (N.of_nat k)) = N2hotv k.
Proof.
  intros.
  (* strategy: for the n -> S n case we (1) bash out the new k's (2) transport the old k s from the smaller n *)
  induction n.
  { inversion H.
    { trivial. }
    { inversion H1. }
  }
  { induction k.
    { Abort.
