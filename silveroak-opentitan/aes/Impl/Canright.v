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
Require Import Cava.Cava.
Require Import AesImpl.Pkg.
Import Vec.BitVecNotations.
Import VectorNotations.
Open Scope bitvec_scope.


Local Notation byte := (Vec Bit 8) (only parsing).
Local Notation "v [@ n ]" := (indexConst v n) (at level 1, format "v [@ n ]").

Section WithCava.
  Context {signal} {semantics : Cava signal}.

  (* // Multiplication in GF(2^2), using normal basis [Omega^2, Omega] *)
  (* // (see Figure 14 in the technical report) *)
  (* function automatic logic [1:0] aes_mul_gf2p2(logic [1:0] g, logic [1:0] d); *)
  (*   logic [1:0] f; *)
  (*   logic       a, b, c; *)
  (*   a    = g[1] & d[1]; *)
  (*   b    = (^g) & (^d); *)
  (*   c    = g[0] & d[0]; *)
  (*   f[1] = a ^ b; *)
  (*   f[0] = c ^ b; *)
  (*   return f; *)
  (* endfunction *)
  Definition aes_mul_gf2p2 (g d: signal (Vec Bit 2)) : cava (signal (Vec Bit 2)) :=
    g0 <- g[@0] ;;
    d0 <- d[@0] ;;
    g1 <- g[@1] ;;
    d1 <- d[@1] ;;
    g' <- xor2 (g0, g1) ;;
    d' <- xor2 (d0, d1) ;;
    a <- and2 (g1, d1) ;;
    b <- and2 (g', d') ;;
    c <- and2 (g0, d0) ;;
    ab <- xor2 (a, b) ;;
    cb <- xor2 (c, b) ;;
    packV [cb; ab].

  (* // Scale by Omega^2 = N in GF(2^2), using normal basis [Omega^2, Omega] *)
  (* // (see Figure 16 in the technical report) *)
  (* function automatic logic [1:0] aes_scale_omega2_gf2p2(logic [1:0] g); *)
  (*   logic [1:0] d; *)
  (*   d[1] = g[0]; *)
  (*   d[0] = g[1] ^ g[0]; *)
  (*   return d; *)
  (* endfunction *)
  Definition aes_scale_omega2_gf2p2 (g: signal (Vec Bit 2)) : cava (signal (Vec Bit 2)) :=
    g0 <- g[@0] ;;
    g1 <- g[@1] ;;
    g' <- xor2 (g0,g1) ;;
    packV [g'; g0].

  (* // Scale by Omega = N^2 in GF(2^2), using normal basis [Omega^2, Omega] *)
  (* // (see Figure 15 in the technical report) *)
  (* function automatic logic [1:0] aes_scale_omega_gf2p2(logic [1:0] g); *)
  (*   logic [1:0] d; *)
  (*   d[1] = g[1] ^ g[0]; *)
  (*   d[0] = g[1]; *)
  (*   return d; *)
  (* endfunction *)
  Definition aes_scale_omega_gf2p2 (g: signal (Vec Bit 2)) : cava (signal (Vec Bit 2)) :=
    g0 <- g[@0] ;;
    g1 <- g[@1] ;;
    g' <- xor2 (g0,g1) ;;
    packV [g1; g'].

  (* // Square in GF(2^2), using normal basis [Omega^2, Omega] *)
  (* // (see Figures 8 and 10 in the technical report) *)
  (* function automatic logic [1:0] aes_square_gf2p2(logic [1:0] g); *)
  (*   logic [1:0] d; *)
  (*   d[1] = g[0]; *)
  (*   d[0] = g[1]; *)
  (*   return d; *)
  (* endfunction *)
  Definition aes_square_gf2p2 (g: signal (Vec Bit 2)) : cava (signal (Vec Bit 2)) :=
    g0 <- g[@0] ;;
    g1 <- g[@1] ;;
    packV [g1; g0].

  (* // Multiplication in GF(2^4), using normal basis [alpha^8, alpha^2] *)
  (* // (see Figure 13 in the technical report) *)
  (* function automatic logic [3:0] aes_mul_gf2p4(logic [3:0] gamma, logic [3:0] delta); *)
  (*   logic [3:0] theta; *)
  (*   logic [1:0] a, b, c; *)
  (*   a          = aes_mul_gf2p2(gamma[3:2], delta[3:2]); *)
  (*   b          = aes_mul_gf2p2(gamma[3:2] ^ gamma[1:0], delta[3:2] ^ delta[1:0]); *)
  (*   c          = aes_mul_gf2p2(gamma[1:0], delta[1:0]); *)
  (*   theta[3:2] = a ^ aes_scale_omega2_gf2p2(b); *)
  (*   theta[1:0] = c ^ aes_scale_omega2_gf2p2(b); *)
  (*   return theta; *)
  (* endfunction *)
  Definition aes_mul_gf2p4 (g d: signal (Vec Bit 4)) : cava (signal (Vec Bit 4)) :=
    g' <- unpackV g ;;
    d' <- unpackV d ;;
    g_hi <- packV (slice_default defaultSignal g' 2 2) ;;
    g_lo <- packV (slice_default defaultSignal g' 0 2) ;;
    d_hi <- packV (slice_default defaultSignal d' 2 2) ;;
    d_lo <- packV (slice_default defaultSignal d' 0 2) ;;
    g_mix <- g_hi ^ g_lo ;;
    d_mix <- d_hi ^ d_lo ;;
    a <- aes_mul_gf2p2 g_hi d_hi ;;
    b <- aes_mul_gf2p2 g_mix d_mix ;;
    c <- aes_mul_gf2p2 g_lo d_lo ;;
    b_scale <- aes_scale_omega2_gf2p2 b ;;
    theta_hi <- a ^ b_scale ;;
    theta_lo <- c ^ b_scale ;;
    theta_hi' <- unpackV theta_hi ;;
    theta_lo' <- unpackV theta_lo ;;
    packV (theta_lo' ++ theta_hi').

  (* // Square and scale by nu in GF(2^4)/GF(2^2), using normal basis [alpha^8, alpha^2] *)
  (* // (see Figure 19 as well as Appendix A of the technical report) *)
  (* function automatic logic [3:0] aes_square_scale_gf2p4_gf2p2(logic [3:0] gamma); *)
  (*   logic [3:0] delta; *)
  (*   logic [1:0] a, b; *)
  (*   a          = gamma[3:2] ^ gamma[1:0]; *)
  (*   b          = aes_square_gf2p2(gamma[1:0]); *)
  (*   delta[3:2] = aes_square_gf2p2(a); *)
  (*   delta[1:0] = aes_scale_omega_gf2p2(b); *)
  (*   return delta; *)
  (* endfunction *)
  Definition aes_square_scale_gf2p4_gf2p2 (g: signal (Vec Bit 4)) : cava (signal (Vec Bit 4)) :=
    g' <- unpackV g ;;
    g_hi <- packV (slice_default defaultSignal g' 2 2) ;;
    g_lo <- packV (slice_default defaultSignal g' 0 2) ;;
    a <- g_hi ^ g_lo ;;
    b <- aes_square_gf2p2 g_lo ;;
    d_hi <- aes_square_gf2p2 a ;;
    d_lo <- aes_scale_omega_gf2p2 b ;;
    d_hi' <- unpackV d_hi ;;
    d_lo' <- unpackV d_lo ;;
    packV (d_lo' ++ d_hi').

  (* // Basis conversion matrices to convert between polynomial basis A, normal basis X *)
  (* // and basis S incorporating the bit matrix of the SBox. More specifically, *)
  (* // multiplication by X2X performs the transformation from normal basis X into *)
  (* // polynomial basis A, followed by the affine transformation (substep 2). Likewise, *)
  (* // multiplication by S2X performs the inverse affine transformation followed by the *)
  (* // transformation from polynomial basis A to normal basis X. *)
  (* // (see Appendix A of the technical report) *)

  (* parameter logic [7:0] A2X [8] = '{8'h98, 8'hf3, 8'hf2, 8'h48, 8'h09, 8'h81, 8'ha9, 8'hff};
  parameter logic [7:0] X2A [8] = '{8'h64, 8'h78, 8'h6e, 8'h8c, 8'h68, 8'h29, 8'hde, 8'h60};
  parameter logic [7:0] X2S [8] = '{8'h58, 8'h2d, 8'h9e, 8'h0b, 8'hdc, 8'h04, 8'h03, 8'h24};
  parameter logic [7:0] S2X [8] = '{8'h8c, 8'h79, 8'h05, 8'heb, 8'h12, 8'h04, 8'h51, 8'h53}; *)

  Definition A2X := natvec_to_signal_sized 8 [ 152; 243; 242;  72;   9; 129; 169; 255 ].
  Definition X2A := natvec_to_signal_sized 8 [ 100; 120; 110; 140; 104;  41; 222;  96 ].
  Definition X2S := natvec_to_signal_sized 8 [  88;  45; 158;  11; 220;   4;   3;  36 ].
  Definition S2X := natvec_to_signal_sized 8 [ 140; 121;   5; 235;  18;   4;  81;  83 ].


  (* function automatic logic [3:0] aes_inverse_gf2p4(logic [3:0] gamma);
    logic [3:0] delta;
    logic [1:0] a, b, c, d;
    a          = gamma[3:2] ^ gamma[1:0];
    b          = aes_mul_gf2p2(gamma[3:2], gamma[1:0]);
    c          = aes_scale_omega2_gf2p2(aes_square_gf2p2(a));
    d          = aes_square_gf2p2(c ^ b);
    delta[3:2] = aes_mul_gf2p2(d, gamma[1:0]);
    delta[1:0] = aes_mul_gf2p2(d, gamma[3:2]);
    return delta;
  endfunction *)
  Definition aes_inverse_gf2p4 (g: signal (Vec Bit 4)) : cava (signal (Vec Bit 4)) :=
    g' <- unpackV g ;;
    g_hi <- packV (slice_default defaultSignal g' 2 2) ;;
    g_lo <- packV (slice_default defaultSignal g' 0 2) ;;
    a <- g_hi ^ g_lo ;;
    b <- aes_mul_gf2p2 g_hi g_lo ;;

    aa <- aes_square_gf2p2 a ;;
    c <- aes_scale_omega2_gf2p2 aa ;;
    cb <- c ^ b  ;;
    d <- aes_square_gf2p2 cb ;;
    d_hi <- aes_mul_gf2p2 d g_lo ;;
    d_lo <- aes_mul_gf2p2 d g_hi ;;
    d_hi' <- unpackV d_hi ;;
    d_lo' <- unpackV d_lo ;;
    packV (d_lo' ++ d_hi').

    (* // Inverse in GF(2^8), using normal basis [d^16, d]
    // (see Figure 11 in the technical report)
    function automatic logic [7:0] aes_inverse_gf2p8(logic [7:0] gamma);
      logic [7:0] delta;
      logic [3:0] a, b, c, d;
      a          = gamma[7:4] ^ gamma[3:0];
      b          = aes_mul_gf2p4(gamma[7:4], gamma[3:0]);
      c          = aes_square_scale_gf2p4_gf2p2(a);
      d          = aes_inverse_gf2p4(c ^ b);
      delta[7:4] = aes_mul_gf2p4(d, gamma[3:0]);
      delta[3:0] = aes_mul_gf2p4(d, gamma[7:4]);
      return delta;
    endfunction *)
  Definition aes_inverse_gf2p8 (g: signal (Vec Bit 8)) : cava (signal (Vec Bit 8)) :=
    g' <- unpackV g ;;
    g_hi <- packV (slice_default defaultSignal g' 4 4) ;;
    g_lo <- packV (slice_default defaultSignal g' 0 4) ;;
    a <- g_hi ^ g_lo ;;
    b <- aes_mul_gf2p4 g_hi g_lo ;;
    c <- aes_square_scale_gf2p4_gf2p2 a ;;
    cb <- c ^ b ;;
    d <- aes_inverse_gf2p4 cb ;;
    d_hi <- aes_mul_gf2p4 d g_lo ;;
    d_lo <- aes_mul_gf2p4 d g_hi ;;
    d_hi' <- unpackV d_hi ;;
    d_lo' <- unpackV d_lo ;;
    packV (d_lo' ++ d_hi').

  Context (aes_mvm: signal (Vec Bit 8) -> signal (Vec (Vec Bit 8) 8) -> cava (signal (Vec Bit 8))).

  (* module aes_sbox_canright (
    input  aes_pkg::ciph_op_e op_i,
    input  logic [7:0]        data_i,
    output logic [7:0]        data_o
  ); *)
  Definition aes_sbox_canright (op_i: signal Bit) (data_i: signal (Vec Bit 8)): cava (signal (Vec Bit 8)) :=
    (* // Convert to normal basis X.
    assign data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X) :
                                              aes_mvm(data_i ^ 8'h63, S2X); *)
    A2X <- A2X ;;
    S2X <- S2X ;;
    X2S <- X2S ;;
    X2A <- X2A ;;
    data_basis_x_fwd <- aes_mvm data_i A2X ;;
    data_i_99 <- data_i ^ (bitvec_to_signal (nat_to_bitvec_sized 8 99)) ;;
    data_basis_x_bwd <- aes_mvm data_i_99 S2X ;;
    data_basis_x <- mux2 op_i (data_basis_x_fwd, data_basis_x_bwd) ;;

    (* // Do the inversion in normal basis X.
    assign data_inverse = aes_inverse_gf2p8(data_basis_x); *)
    data_inverse <- aes_inverse_gf2p8 data_basis_x ;;

    (* // Convert to basis S or A.
    assign data_o       = (op_i == CIPH_FWD) ? aes_mvm(data_inverse, X2S) ^ 8'h63 :
                                              aes_mvm(data_inverse, X2A);  *)
    data_o_fwd' <- aes_mvm data_inverse X2S ;;
    data_o_fwd <- data_o_fwd' ^ (bitvec_to_signal (nat_to_bitvec_sized 8 99)) ;;
    data_o_bwd <- aes_mvm data_inverse X2A ;;
    mux2 op_i (data_o_fwd, data_o_bwd).

End WithCava.
