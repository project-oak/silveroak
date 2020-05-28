(* TODO:

An aspirational direct translation to work towards. Currently not working.

*)
Require Import Cava.Netlist.

Require Import Cava.Arrow.Arrow.
Require Import Cava.Arrow.Syntax.

Open Scope source.

(* function automatic logic [7:0] aes_mul2(logic [7:0] in); *)
(*   logic [7:0] out; *)
(*   out[7] = in[6]; *)
(*   out[6] = in[5]; *)
(*   out[5] = in[4]; *)
(*   out[4] = in[3] ^ in[7]; *)
(*   out[3] = in[2] ^ in[7]; *)
(*   out[2] = in[1]; *)
(*   out[1] = in[0] ^ in[7]; *)
(*   out[0] = in[7]; *)
(*   return out; *)
(* endfunction *)
Definition aes_mult2
  : Kappa (bitvec [8] ** unit) (bitvec [8]) := <[
  \x =>
  bitvec
    ( x[6]
    , x[5]
    , x[4]
    , x[3] ^ x[7]
    , x[2] ^ x[7]
    , x[1]
    , x[0] ^ x[7]
    , x[7]
    )
]>.

Definition aes_mult4
  : Kappa (bitvec [8] ** unit) (bitvec [8]) := <[
  \x => aes_mul2 (aes_mul2 x)
]>.

(* function automatic logic [7:0] aes_div2(logic [7:0] in); *)
(*   logic [7:0] out; *)
(*   out[7] = in[0]; *)
(*   out[6] = in[7]; *)
(*   out[5] = in[6]; *)
(*   out[4] = in[5]; *)
(*   out[3] = in[4] ^ in[0]; *)
(*   out[2] = in[3] ^ in[0]; *)
(*   out[1] = in[2]; *)
(*   out[0] = in[1] ^ in[0]; *)
(*   return out; *)
(* endfunction *)
Definition aes_div2
  : Kappa (bitvec [8] ** unit) (bitvec [8]) := <[
  \x =>
  bitvec
    ( x[0]
    , x[7]
    , x[6]
    , x[5]
    , x[4] ^ x[0]
    , x[3] ^ x[0]
    , x[2]
    , x[1] ^ x[0]
    )
]>.

(* function automatic logic [31:0] aes_circ_byte_shift(logic [31:0] in, logic [1:0] shift); *)
(*   logic [31:0] out; *)
(*   logic [31:0] s; *)
(*   s = {30'b0,shift}; *)
(*   out = {in[8*((7-s)%4) +: 8], in[8*((6-s)%4) +: 8], *)
(*          in[8*((5-s)%4) +: 8], in[8*((4-s)%4) +: 8]}; *)
(*   return out; *)
(* endfunction *)
Definition aes_circ_byte_shift
  : Kappa (bitvec [32] ** bitvec [2] ** unit) (bitvec [32]) := <[
  \value shift =>
  let s = concat ( 0 : bitvec 30 ) shift in
  concat
    (concat
      value[8*((7-s)%4) +: 8]
      value[8*((6-s)%4) +: 8])
    (concat
      value[8*((5-s)%4) +: 8]
      value[8*((4-s)%4) +: 8])
]>.

(* function automatic logic [3:0][3:0][7:0] aes_transpose(logic [3:0][3:0][7:0] in); *)
(*   logic [3:0][3:0][7:0] transpose; *)
(*   transpose = '0; *)
(*   for (int j=0; j<4; j++) begin *)
(*     for (int i=0; i<4; i++) begin *)
(*       transpose[i][j] = in[j][i]; *)
(*     end *)
(*   end *)
(*   return transpose; *)
(* endfunction *)
Definition aes_transpose 
  : Kappa (bitvec [4;4;8] ** unit) (bitvec [4;4;8]) := 
  reshape (concat_bitvec
  (map (fun j => 
    map (fun i => 
      <[ \x => x[j][i] ]>.
    ) (seq 0 4)
  ) (seq 0 4)
  )
  ).


(* function automatic logic [3:0][7:0] aes_col_get(logic [3:0][3:0][7:0] in, logic [1:0] idx); *)
(*   logic [3:0][7:0] out; *)
(*   for (int i=0; i<4; i++) begin *)
(*     out[i] = in[i][idx]; *)
(*   end *)
(*   return out; *)
(* endfunction *)
Definition aes_col_get 
  : Kappa (bitvec [4;4;8] ** bitvec[2] ** unit) (bitvec [4;8]) := 

  concat_bitvec
  (map (fun j => 
      <[ \x idx => x[j][idx] ]>.
  ) (seq 0 4)
  ).

(* function automatic logic [7:0] aes_mvm( *)
(*   logic [7:0] vec_b, *)
(*   logic [7:0] mat_a [8] *)
(* ); *)
(*   logic [7:0] vec_c; *)
(*   vec_c = '0; *)
(*   for (int i=0; i<8; i++) begin *)
(*     for (int j=0; j<8; j++) begin *)
(*       vec_c[i] = vec_c[i] ^ (mat_a[j][i] & vec_b[7-j]); *)
(*     end *)
(*   end *)
(*   return vec_c; *)
(* endfunction *)

Definition aes_mvm_acc
  (j: bitvec [3])
  : Kappa (bitvec [8] ** bitvec[8][8] ** bitvec[8] ** unit) (bitvec [8]) := 
  (map (fun i => 
      <[ \vector matrix acc => acc[i] ^ (matrix[j][i] & vector[7-j]) ]>.
  ) (seq 0 4)
  ).

Definition aes_mvm
  : Kappa (bitvec [8] ** bitvect [8][8] ** unit) (bitvec [8]) := 
  fold (fun i acc => aes_mvm_acc i) <[constant_vec 0]> (seq 0 4).