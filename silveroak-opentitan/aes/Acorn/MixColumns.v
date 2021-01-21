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
Require Import AcornAes.Pkg.
Require Import AesSpec.StateTypeConversions.
Require Import AesSpec.Tests.CipherTest.
Require Import AesSpec.Tests.Common.
Import Common.Notations.

Import VectorNotations.

Local Notation byte := (Vec Bit 8) (only parsing).
Local Notation "v [@ n ]" := (indexConst v n) (at level 1, format "v [@ n ]").

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {monad: Monad cava}.

  Definition zero_byte : cava (signal byte) :=
    z <- zero ;;
    ret (unpeel (z :: z :: z :: z :: z :: z :: z :: z :: [])).

  Definition aes_mix_single_column
    (op_i: signal Bit) (data_i: signal (Vec byte 4))
    : cava (signal (Vec byte 4)) :=
    let x :=
      (data_i[@0], data_i[@3]) ::
      (data_i[@3], data_i[@2]) ::
      (data_i[@2], data_i[@1]) ::
      (data_i[@1], data_i[@0]) :: [] in
    x <- mapT xor' x ;;

    x_mul2 <- mapT aes_mul2 x ;;
    let x_mul2 := unpeel x_mul2 in

    y_pre_mul4_0 <- xor data_i[@3] data_i[@1] ;;
    y_pre_mul4_1 <- xor data_i[@3] data_i[@1] ;;
    y <- mapT aes_mul4 (y_pre_mul4_0 :: y_pre_mul4_1 :: []) ;;
    let y := unpeel y in

    y2_pre_mul2 <- xor y[@0] y[@1] ;;
    y2 <- aes_mul2 y2_pre_mul2 ;;

    z_0 <- xor y2 y[@0] ;;
    z_1 <- xor y2 y[@1] ;;
    let z := unpeel (z_0 :: z_1 :: []) in

    op_i_inv <- inv op_i ;;

    zb <- zero_byte;;

    let paired := unpeel (unpeel (zb :: zb :: []) :: z :: []) in
    let z_muxed := indexAt paired (unpeel (op_i :: [])) in

    let x := unpeel x in

    data_o0 <- (xor data_i[@1] x_mul2[@3] >>= xor x[@1] >>= xor z_muxed[@1]) ;;
    data_o1 <- (xor data_i[@0] x_mul2[@2] >>= xor x[@1] >>= xor z_muxed[@0]) ;;
    data_o2 <- (xor data_i[@3] x_mul2[@1] >>= xor x[@3] >>= xor z_muxed[@1]) ;;
    data_o3 <- (xor data_i[@2] x_mul2[@0] >>= xor x[@3] >>= xor z_muxed[@0]) ;;

    ret (unpeel (data_o0 :: data_o1 :: data_o2 :: data_o3 :: [])).

  Definition aes_mix_columns
    (op_i : signal Bit) (a: signal (Vec (Vec (Vec Bit 8) 4) 4))
    : cava (signal (Vec (Vec (Vec Bit 8) 4) 4)) :=
  let transposed := aes_transpose a in
  mixed <- mapT (aes_mix_single_column op_i) (peel transposed) ;;
  ret (aes_transpose (unpeel mixed)).

End WithCava.
