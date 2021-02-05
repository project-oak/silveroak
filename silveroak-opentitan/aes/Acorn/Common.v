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

Require Import Cava.Signal.

Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Ndigits.
Require Import Cava.BitArithmetic.

Module Notations.
  Notation state := (Vec (Vec (Vec Bit 8) 4) 4) (only parsing).
  Notation key := (Vec (Vec (Vec Bit 8) 4) 4) (only parsing).
End Notations.

(* A function to convert a matrix of nat values to a value of type state *)
Definition fromNatState (i : Vector.t (Vector.t nat 4) 4 ): Vector.t (Vector.t Byte.byte 4) 4
  := Vector.map (Vector.map (fun v => bitvec_to_byte (N2Bv_sized 8 (N.of_nat v)))) i.

(* A function to convert a state value to a matrix of nat values. *)
Definition toNatState (i: Vector.t (Vector.t Byte.byte 4) 4) : Vector.t (Vector.t nat 4) 4
  := Vector.map (Vector.map (fun v => N.to_nat (Bv2N (byte_to_bitvec v)))) i.

(* A function to convert a matrix of nat values to a matrix of bitvecs *)
Definition fromNatVec (i : Vector.t (Vector.t nat 4) 4 ): Vector.t (Vector.t (Vector.t bool 8) 4) 4
  := Vector.map (Vector.map (fun v => N2Bv_sized 8 (N.of_nat v))) i.

(* A function to convert a bitvec matrix to a nat matrix. *)
Definition toNatVec (i: Vector.t (Vector.t (Vector.t bool 8) 4) 4) : Vector.t (Vector.t nat 4) 4
  := Vector.map (Vector.map (fun v => N.to_nat (Bv2N v))) i.
