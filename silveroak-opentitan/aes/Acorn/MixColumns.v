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
Require Import AesSpec.Tests.CipherTest.
Require Import AesSpec.Tests.Common.
Require Import AesSpec.StateTypeConversions.
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
    (*
    //
    // AES MixColumns for one single column of the state matrix
    //
    // For details, see Equations 4-7 of:
    // Satoh et al., "A Compact Rijndael Hardware Architecture with S-Box Optimization"
    *)

    (* // Drive x *)
    (* assign x[0] = data_i[0] ^ data_i[3]; *)
    (* assign x[1] = data_i[3] ^ data_i[2]; *)
    (* assign x[2] = data_i[2] ^ data_i[1]; *)
    (* assign x[3] = data_i[1] ^ data_i[0]; *)

    let x :=
      (data_i[@0], data_i[@3]) ::
      (data_i[@3], data_i[@2]) ::
      (data_i[@2], data_i[@1]) ::
      (data_i[@1], data_i[@0]) :: [] in
    x <- mapT xor' x ;;

    (* // Mul2(x) *)
    (*   for (genvar i = 0; i < 4; i++) begin : gen_x_mul2 *)
    (*     assign x_mul2[i] = aes_mul2(x[i]); *)
    (*   end *)
    x_mul2 <- mapT aes_mul2 x ;;
    let x := unpeel x in
    let x_mul2 := unpeel x_mul2 in


    (* // Drive y_pre_mul4 *)
    (* assign y_pre_mul4[0] = data_i[3] ^ data_i[1]; *)
    (* assign y_pre_mul4[1] = data_i[2] ^ data_i[0]; *)
    y_pre_mul4_0 <- xor data_i[@3] data_i[@1] ;;
    y_pre_mul4_1 <- xor data_i[@3] data_i[@1] ;;
    (* // Mul4(y_pre_mul4) *)
    (* for (genvar i = 0; i < 2; i++) begin : gen_mul4 *)
    (*   assign y[i] = aes_mul4(y_pre_mul4[i]); *)
    (* end *)
    y <- mapT aes_mul4 (y_pre_mul4_0 :: y_pre_mul4_1 :: []) ;;
    let y := unpeel y in

    (* // Drive y2_pre_mul2 *)
    (* assign y2_pre_mul2 = y[0] ^ y[1]; *)
    y2_pre_mul2 <- xor y[@0] y[@1] ;;
    (* // Mul2(y) *)
    (* assign y2 = aes_mul2(y2_pre_mul2); *)
    y2 <- aes_mul2 y2_pre_mul2 ;;

    (* // Drive z *)
    (* assign z[0] = y2 ^ y[0]; *)
    (* assign z[1] = y2 ^ y[1]; *)
    z_0 <- xor y2 y[@0] ;;
    z_1 <- xor y2 y[@1] ;;
    let z := unpeel (z_0 :: z_1 :: []) in


    (* // Mux z *)
    (* assign z_muxed[0] = (op_i == CIPH_FWD) ? 8'b0 : z[0]; *)
    (* assign z_muxed[1] = (op_i == CIPH_FWD) ? 8'b0 : z[1]; *)
    op_i_inv <- inv op_i ;; (* CIPH_FWD := false *)
    zb <- zero_byte;;
    let paired := unpeel (unpeel (zb :: zb :: []) :: z :: []) in
    let z_muxed := indexAt paired (unpeel (op_i :: [])) in

    (* // Drive outputs *)
    (* assign data_o[0] = data_i[1] ^ x_mul2[3] ^ x[1] ^ z_muxed[1]; *)
    (* assign data_o[1] = data_i[0] ^ x_mul2[2] ^ x[1] ^ z_muxed[0]; *)
    (* assign data_o[2] = data_i[3] ^ x_mul2[1] ^ x[3] ^ z_muxed[1]; *)
    (* assign data_o[3] = data_i[2] ^ x_mul2[0] ^ x[3] ^ z_muxed[0]; *)
    data_o0 <- (xor data_i[@1] x_mul2[@3] >>= xor x[@1] >>= xor z_muxed[@1]) ;;
    data_o1 <- (xor data_i[@0] x_mul2[@2] >>= xor x[@1] >>= xor z_muxed[@0]) ;;
    data_o2 <- (xor data_i[@3] x_mul2[@1] >>= xor x[@3] >>= xor z_muxed[@1]) ;;
    data_o3 <- (xor data_i[@2] x_mul2[@0] >>= xor x[@3] >>= xor z_muxed[@0]) ;;

    ret (unpeel (data_o0 :: data_o1 :: data_o2 :: data_o3 :: [])).

  Definition aes_mix_columns
    (op_i : signal Bit) (a: signal (Vec (Vec (Vec Bit 8) 4) 4))
    : cava (signal (Vec (Vec (Vec Bit 8) 4) 4)) :=
    (* // Transpose to operate on columns
    logic [3:0][3:0][7:0] data_i_transposed;
    logic [3:0][3:0][7:0] data_o_transposed;

    assign data_i_transposed = aes_transpose(data_i);

    // Individually mix columns
    for (genvar i = 0; i < 4; i++) begin : gen_mix_column
      aes_mix_single_column aes_mix_column_i (
        .op_i   ( op_i                 ),
        .data_i ( data_i_transposed[i] ),
        .data_o ( data_o_transposed[i] )
      );
    end

    assign data_o = aes_transpose(data_o_transposed); *)
    let transposed := aes_transpose a in
    mixed <- mapT (aes_mix_single_column op_i) (peel transposed) ;;
    ret (aes_transpose (unpeel mixed)).

End WithCava.

(* Run test as a quick-feedback check *)
Require Import Cava.BitArithmetic.
Require Import AesSpec.StateTypeConversions.

Import List.ListNotations.
Goal
  (let signal := combType in
  let to_state : Vector.t bool 128 -> signal state :=
      fun st => Vector.map (Vector.map (fun r => byte_to_bitvec r)) (BigEndian.to_rows st) in
  let from_state : signal state -> Vector.t bool 128 :=
      fun st => BigEndian.from_rows (Vector.map (Vector.map (fun r => bitvec_to_byte r)) st) in

   (* run encrypt test with this version of aes_mix_columns plugged in *)
   aes_test_encrypt Matrix
                    (fun step key =>
                       match step with
                       | MixColumns =>
                         fun st =>
                           let input := to_state st in
                           let output := unIdent (aes_mix_columns [false]%list [input]%list) in
                           from_state (List.hd (defaultCombValue _) output)
                       | _ => aes_impl step key
                       end) = Success).
Proof. vm_compute. reflexivity. Qed.
