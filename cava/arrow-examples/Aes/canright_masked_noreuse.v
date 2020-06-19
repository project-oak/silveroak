(* Note: original implementation has circuit ordering requirements for safety 
which are likely violated here *)

Require Import Cava.Arrow.Kappa.Syntax.
Require Import Cava.Arrow.Arrow.

From Coq Require Import NArith Lia.

Import KappaNotation.

Require Import Util.
Require Import pkg.
Require Import canright_pkg.

Section var.
Variable var: Kind -> Kind -> Type.

(* function automatic logic [3:0] aes_masked_inverse_gf2p4(logic [3:0] b,
                                                        logic [3:0] q,
                                                        logic [1:0] r,
                                                        logic [3:0] t);*)
Definition aes_masked_inverse_gf2p4
  : kappa_sugared var
    << Vector 4 Bit (* b *)
    ,  Vector 4 Bit (* q *)
    ,  Vector 2 Bit (* r *)
    ,  Vector 4 Bit (* t *)
    ,  Unit >> 
    <<Vector 4 Bit>>. refine (
<[ \b q r t =>
    let b1 = b[3:2] in
    let b0 = b[1:0] in
    let q1 = q[3:2] in
    let q0 = q[1:0] in
    let t1 = t[3:2] in
    let t0 = t[1:0] in

    (* // Formula 13
    // IMPORTANT: The following ops must be executed in order (left to right):
    c = r ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(b1 ^ b0))
          ^ aes_scale_omega2_gf2p2(aes_square_gf2p2(q1 ^ q0))
          ^ aes_mul_gf2p2(b1, b0)
          ^ aes_mul_gf2p2(b1, q0) ^ aes_mul_gf2p2(b0, q1) ^ aes_mul_gf2p2(q1, q0); *)
    let temp1 = !aes_scale_omega2_gf2p2 (!aes_square_gf2p2 (b1 ^ b0)) in
    let temp2 = !aes_scale_omega2_gf2p2 (!aes_square_gf2p2 (q1 ^ q0)) in 
    let temp3 = !aes_mul_gf2p2 b1 b0 in 
    let temp4 = !aes_mul_gf2p2 b1 q0 ^ !aes_mul_gf2p2 b0 q1 ^ !aes_mul_gf2p2 q1 q0 in

    let c = r ^ temp1 ^ temp2 ^ temp3 ^ temp4 in

    (* // Formulas 14 and 15
    c_inv = aes_square_gf2p2(c);
    r_sq  = aes_square_gf2p2(r); *)

    let c_inv = !aes_square_gf2p2 c in
    let r_sq  = !aes_square_gf2p2 r in

    (* // Formulas 16 and 17
    // IMPORTANT: The following ops must be executed in order (left to right):
    b1_inv = t1 ^ aes_mul_gf2p2(b0, c_inv)
                ^ aes_mul_gf2p2(b0, r_sq) ^ aes_mul_gf2p2(q0, c_inv) ^ aes_mul_gf2p2(q0, r_sq);
    b0_inv = t0 ^ aes_mul_gf2p2(b1, c_inv)
                ^ aes_mul_gf2p2(b1, r_sq) ^ aes_mul_gf2p2(q1, c_inv) ^ aes_mul_gf2p2(q1, r_sq);
    // *)

    let b1_inv = t1 ^ !aes_mul_gf2p2 b0 c_inv
                    ^ !aes_mul_gf2p2 b0 r_sq ^ !aes_mul_gf2p2 q0 c_inv ^ !aes_mul_gf2p2 q0 r_sq in
    let b0_inv = t0 ^ !aes_mul_gf2p2 b1 c_inv
                    ^ !aes_mul_gf2p2 b1 r_sq ^ !aes_mul_gf2p2 q1 c_inv ^ !aes_mul_gf2p2 q1 r_sq in

    (* // Note: b_inv is masked by t, b was masked by q.
    b_inv = {b1_inv, b0_inv}; *)

    concat b0_inv b1_inv

]>); lia.
Defined.

Definition aes_masked_inverse_gf2p8
  : kappa_sugared var
    << Vector 8 Bit (* a *)
    ,  Vector 8 Bit (* m *)
    ,  Vector 8 Bit (* n *)
    ,  Unit >> 
    <<Vector 8 Bit>>. refine (
<[ \a m n =>
    let a1 = a[7:4] in
    let a0 = a[3:0] in
    let m1 = m[7:4] in
    let m0 = m[3:0] in

    (* // q must be independent of m. *)
    let q = n[7:4] in

    (* // Formula 12
    // IMPORTANT: The following ops must be executed in order (left to right):
    b = q ^ aes_square_scale_gf2p4_gf2p2(a1 ^ a0)
          ^ aes_square_scale_gf2p4_gf2p2(m1 ^ m0)
          ^ aes_mul_gf2p4(a1, a0)
          ^ aes_mul_gf2p4(a1, m0) ^ aes_mul_gf2p4(a0, m1) ^ aes_mul_gf2p4(m1, m0); *)
    
    let b = q ^ !aes_square_scale_gf2p4_gf2p2 (a1 ^ a0)
              ^ !aes_square_scale_gf2p4_gf2p2 (m1 ^ m0)
              ^ !aes_mul_gf2p4 a1 a0
              ^ !aes_mul_gf2p4 a1 m0 ^ !aes_mul_gf2p4 a0 m1 ^ !aes_mul_gf2p4 m1 m0 in

    (* // r must be independent of q. *)
    let r = m1[3:2] in

    (* // Note that the paper states the following requirements on t:
    // - t must be independent of r.
    // - t1 must be independent of q0, t0 must be independent of q1.
    // - t must be independent of m (for the final steps involving s)
    // The paper suggests to use t = q. To select s = n for the output mask (s must be independent
    // of t = q = n[7:4]), we would need t = m0 or similar (not r, m1[3:2] though), but this would
    // break the random product distribution of aes_mul_gf2p4(m0, t), or aes_mul_gf2p4(m1, t) below
    // (see Lemma 2 in the paper). For this reason, we select t = q here and apply a final mask
    // switch from s = m to n after the inversion.
    t = q; *)
    let t = q in

    (* // b is masked by q, b_inv is masked by t. *)
    let b_inv = !aes_masked_inverse_gf2p4 b q r t in

    (* // Note that the paper states the following requirements on s:
    // - s must be independent of t
    // - s1 must be independent of m0, s0 must be independent of m1.
    // The paper suggests to use s = m (the input mask). To still end up with the specified output
    // mask n, we will apply a final mask switch after the inversion.
    s1 = m1;
    s0 = m0; *)
    let s1 = m1 in
    let s0 = m0 in

    (* // Formulas 18 and 19
    // IMPORTANT: The following ops must be executed in order (left to right):
    a1_inv = s1 ^ aes_mul_gf2p4(a0, b_inv)
                ^ aes_mul_gf2p4(a0, t) ^ aes_mul_gf2p4(m0, b_inv) ^ aes_mul_gf2p4(m0, t);
    a0_inv = s0 ^ aes_mul_gf2p4(a1, b_inv)
                ^ aes_mul_gf2p4(a1, t) ^ aes_mul_gf2p4(m1, b_inv) ^ aes_mul_gf2p4(m1, t);
    // *)
    let a1_inv = s1 ^ !aes_mul_gf2p4 a0 b_inv
                    ^ !aes_mul_gf2p4 a0 t ^ !aes_mul_gf2p4 m0 b_inv ^ !aes_mul_gf2p4 m0 t in
    let a0_inv = s0 ^ !aes_mul_gf2p4 a1 b_inv
                    ^ !aes_mul_gf2p4 a1 t ^ !aes_mul_gf2p4 m1 b_inv ^ !aes_mul_gf2p4 m1 t in

    (* // Note: a_inv is now masked by s = m, a was masked by m. *)
    let a_inv = concat a0_inv a1_inv in

    (* // To have a_inv masked by n (the specified output mask), we perform a final mask switch.
    // IMPORTANT: The following ops must be executed in order (left to right):
    a_inv = a_inv ^ n ^ m; *)
    let a_inv' = a_inv ^ n ^ m in

    a_inv'
]>); lia.
Defined.

Definition aes_sbox_canright_masked_noreuse
  : kappa_sugared var << 
    Vector 1 Bit, (* TODO: wrapped type?  aes_pkg::ciph_op_e op_i, *)

    Vector 8 Bit, (* data_i, // masked, the actual input data is data_i ^ in_mask_i *)
    Vector 8 Bit, (* in_mask_i,  // input mask, independent from actual input data *)
    Vector 8 Bit, (* out_mask_i, // output mask, independent from input mask *)
    Unit >> << Vector 8 Bit>> :=
<[ \op_i data_i in_mask_i out_mask_i =>
    (* // Convert data to normal basis X.
    assign data_basis_x = (op_i == CIPH_FWD) ? aes_mvm(data_i, A2X) :
                                              aes_mvm(data_i ^ 8'h63, S2X); *)
    let data_basis_x = if op_i == !CIPH_FWD
                       then !aes_mvm data_i !A2X
                       else !aes_mvm (data_i ^ #99) !S2X in

    (* // Convert masks to normal basis X.
    // The addition of constant 8'h63 following the affine transformation is skipped.
    assign in_mask_basis_x  = (op_i == CIPH_FWD) ? aes_mvm(in_mask_i, A2X) :
                                                  aes_mvm(in_mask_i, S2X); *)
    let in_mask_basis_x = if op_i == !CIPH_FWD
                          then !aes_mvm in_mask_i !A2X 
                          else !aes_mvm in_mask_i !S2X in

    (* // The output mask is converted in the opposite direction.
    assign out_mask_basis_x = (op_i == CIPH_INV) ? aes_mvm(out_mask_i, A2X) :
                                                  aes_mvm(out_mask_i, S2X); *)
    let out_mask_basis_x = if op_i == !CIPH_INV
                           then !aes_mvm out_mask_i !A2X
                           else !aes_mvm out_mask_i !S2X in

    (* // Do the inversion in normal basis X.
    assign data_inverse = aes_masked_inverse_gf2p8(data_basis_x, in_mask_basis_x, out_mask_basis_x); *)
    let data_inverse = !aes_masked_inverse_gf2p8 data_basis_x in_mask_basis_x out_mask_basis_x in

    (* // Convert to basis S or A.
    assign data_o = (op_i == CIPH_FWD) ? (aes_mvm(data_inverse, X2S) ^ 8'h63) :
                                        (aes_mvm(data_inverse, X2A)); *)
    let data_o = if op_i == !CIPH_FWD
                 then !aes_mvm data_inverse !X2S ^ #99
                 else !aes_mvm data_inverse !X2A
                 in

    data_o
]>.

End var.
