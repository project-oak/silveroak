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

Section WithCava.
  Context {signal} `{Cava signal}.

  (* Check if [inp] is bit-equal to the first [n] bits of [v] *)
  (* TODO(atondwal): use [Fin] to disallow numbers larger than [2^n]. c.f. [ex5] *)
  Definition vecConstEq (n v: nat)
                        (inp: signal (Vec Bit n)) :
                        cava (signal Bit) :=
    const <- Vec.bitvec_literal (N2Bv_sized n (N.of_nat v)) ;;
    eqb (inp, const).

End WithCava.


Example ex1 : vecConstEq 8 42 =<< Vec.bitvec_literal (N2Bv_sized 8 42) = ret true.
Proof. trivial. Qed.

Example ex2 : vecConstEq 8 43 =<< Vec.bitvec_literal (N2Bv_sized 8 42) = ret false.
Proof. trivial. Qed.

Example ex3 : vecConstEq 1 1 =<< Vec.bitvec_literal (N2Bv_sized 1 1) = ret true.
Proof. trivial. Qed.

Example ex4 : vecConstEq 1 1 =<< Vec.bitvec_literal (N2Bv_sized 1 0) = ret false.
Proof. trivial. Qed.

Example ex5 : vecConstEq 1 3 =<< Vec.bitvec_literal (N2Bv_sized 1 1) = ret true.
Proof. trivial. Qed.

