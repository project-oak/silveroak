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

Require Import Cava.Cava.
Require Import AesImpl.Pkg.
Import Pkg.Notations.

Section WithCava.
  Context {signal} {semantics : Cava signal}.

  (* Perform the bitwise XOR of two 4-element vectors of 8-bit values. *)
  Definition xor4xV
      (ab : signal (Vec (Vec Bit 8) 4) * signal (Vec (Vec Bit 8) 4))
      : cava (signal (Vec (Vec Bit 8) 4)) :=
    Vec.map2 xorV (fst ab) (snd ab).

  (* Perform the bitwise XOR of two 4x4 matrices of 8-bit values. *)
  Definition xor4x4V (a b : signal state) : cava (signal state) :=
    Vec.map2 xor4xV a b.

  Definition aes_add_round_key (k : signal key) (st : signal state)
    : cava (signal state) := xor4x4V k st.
End WithCava.
