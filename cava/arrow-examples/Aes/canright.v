Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Arrow.

From Coq Require Import NArith Lia.

Import KappaNotation.

Require Import Util.
Require Import pkg.
Require Import canright_pkg.

Section var.
Variable var: Kind -> Kind -> Type.

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
Program Definition aes_inverse_gf2p4
  : kappa_sugared var <<Vector 4 Bit, Unit>> (Vector 4 Bit) :=
  <[\ gamma =>
      let a = (gamma[3:2]) ^ (gamma[1:0]) in
      let b = !aes_mul_gf2p2 (gamma[3:2]) (gamma[1:0]) in
      let c = !aes_scale_omega2_gf2p2 (!aes_square_gf2p2 a) in
      let d = !aes_square_gf2p2 (c ^ b) in
      concat 
        (!aes_mul_gf2p2 d (gamma[3:2]))
        (!aes_mul_gf2p2 d (gamma[1:0]))
  ]>.

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
Program Definition aes_inverse_gf2p8
  : kappa_sugared var <<Vector 8 Bit, Unit>> (Vector 8 Bit) :=
  <[\ gamma =>
      let a = (gamma[7:4]) ^ (gamma[3:0]) in
      let b = !aes_mul_gf2p4 (gamma[7:4]) (gamma[3:0]) in
      let c = !aes_square_scale_gf2p4_gf2p2 a in
      let d = !aes_inverse_gf2p4 (c ^ b) in

      concat 
        (!aes_mul_gf2p4 d (gamma[7:4]))
        (!aes_mul_gf2p4 d (gamma[3:0]))
  ]>.

(* module aes_sbox_canright (
  input  aes_pkg::ciph_op_e op_i,
  input  logic [7:0]        data_i,
  output logic [7:0]        data_o
); *)
Definition aes_sbox_canright
  : kappa_sugared var << Vector 1 Bit, Vector 8 Bit, Unit>> (Vector 8 Bit) := 
  <[\ op_i data_i =>
      (* // Convert to normal basis X.
      assign data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X) :
                                                aes_mvm(data_i ^ 8'h63, S2X); *)
      let data_basis_x = if op_i == !CIPH_FWD
                         then !aes_mvm data_i !A2X
                         else !aes_mvm (data_i ^ #99) !S2X in

      (* // Do the inversion in normal basis X.
      assign data_inverse = aes_inverse_gf2p8(data_basis_x); *)
      let data_inverse = !aes_inverse_gf2p8 data_basis_x in

      (* // Convert to basis S or A.
      assign data_o       = (op_i == CIPH_FWD) ? aes_mvm(data_inverse, X2S) ^ 8'h63 :
                                                aes_mvm(data_inverse, X2A);  *)
      let data_o = if op_i == !CIPH_FWD
                   then (!aes_mvm data_inverse !X2S) ^ #99
                   else !aes_mvm data_inverse !X2A in

      data_o 
  ]>.

End var.