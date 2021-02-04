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

Require Import Coq.Vectors.Vector.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.

Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Lib.BitVectorOps.
Require Import AcornAes.Common.
Require Import AesSpec.StateTypeConversions.
Require Import AesSpec.Tests.CipherTest.
Require Import AesSpec.Tests.Common.
Import Common.Notations.

Import VectorNotations.

Local Notation byte := (Vec Bit 8) (only parsing).
Local Notation "v [@ n ]" := (indexConst v n) (at level 1, format "v [@ n ]").

Section WithCava.
  Context {signal} {semantics : Cava signal}.

  Definition aes_transpose {n m}
      (matrix : signal (Vec (Vec byte n) m))
      : (signal (Vec (Vec byte m) n)) :=
    let columns := peel matrix in
    let items := map peel columns in
    let columns := map unpeel (transpose items) in
    unpeel columns.

  Definition aes_mul2
    (x : signal byte)
    : cava (signal byte) :=

    a <- xor2 (x[@0], x[@7]) ;;
    b <- xor2 (x[@2], x[@7]) ;;
    c <- xor2 (x[@3], x[@7]) ;;

    ret (unpeel
          [x[@7];
           a;
           x[@1];
           b;
           c;
           x[@4];
           x[@5];
           x[@6]
          ]
    ).

  Definition aes_mul4
    : signal byte -> cava (signal byte) :=
    aes_mul2 >=> aes_mul2.

  Definition zero_byte : signal byte := unpeel (Vector.const zero 8).

  (* function automatic logic [31:0] aes_circ_byte_shift(logic [31:0] in, logic [1:0] shift);
    logic [31:0] out;
    logic [31:0] s;
    s = {30'b0,shift};
    out = {in[8*((7-s)%4) +: 8], in[8*((6-s)%4) +: 8],
           in[8*((5-s)%4) +: 8], in[8*((4-s)%4) +: 8]};
    return out;
  endfunction *)
  Definition aes_circ_byte_shift (shift: nat) (input: signal (Vec byte 4)):
    cava (signal (Vec byte 4)) :=
    let indices := [4 - shift; 5 - shift; 6 - shift; 7 - shift] in
    let indices := map (fun x => Nat.modulo x 4) indices in
    ret (unpeel (map (indexConst input) indices)).

End WithCava.
