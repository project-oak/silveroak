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

From Coq Require Import Arith Eqdep_dec Vector Lia NArith Omega String Ndigits.
From Cava Require Import Arrow.ArrowExport BitArithmetic.

Import VectorNotations.
Import KappaNotation.
Open Scope kind_scope.
Open Scope category_scope.

Notation "|^ x" :=
  (App (RemoveContext (foldr1 <[\a b => xor a b]> _)) x)
  (in custom expr at level 5, no associativity) : kappa_scope.
Notation "x && y" :=
  (App (App (Primitive And) x) y)
  (in custom expr at level 6, left associativity) : kappa_scope.
Notation "x || y" :=
  (App (App (Primitive And) x) y)
  (in custom expr at level 6, left associativity) : kappa_scope.
Notation "x & y" :=
  (App (App (RemoveContext (bitwise <[and]>  _)) x) y)
  (in custom expr at level 6, left associativity) : kappa_scope.
Notation "x ^ y" :=
  (App (App (RemoveContext (bitwise <[xor]> _)) x) y)
    (in custom expr at level 6, left associativity) : kappa_scope.
Notation "'if' i 'then' t 'else' e" :=
  (App (App (App (RemoveContext (mux_item _)) i) t) e)
  (in custom expr at level 5, left associativity) : kappa_scope.
Notation "x == y" :=
  (App (App (RemoveContext (equality _)) x) y)
  (in custom expr at level 6, left associativity) : kappa_scope.

Inductive SboxImpl :=
| SboxLut
| SboxCanright
(* | SboxCanrightMasked *)
| SboxCanrightMaskedNoReuse.

(* typedef enum logic {
  CIPH_FWD = 1'b0,
  CIPH_INV = 1'b1
} ciph_op_e; *)
Definition ciph_op_e := Bit.
Definition CIPH_FWD: Unit ~> ciph_op_e := <[ false' ]>.
Definition CIPH_INV: Unit ~> ciph_op_e := <[ true' ]>.

(* typedef enum logic [1:0] { *)
(*   STATE_INIT, *)
(*   STATE_ROUND, *)
(*   STATE_CLEAR *)
(* } state_sel_e; *)
Definition state_sel_e := Vector Bit 2.
Definition STATE_INIT: Unit ~> state_sel_e := <[ #0 ]>.
Definition STATE_ROUND: Unit ~> state_sel_e := <[ #1 ]>.
Definition STATE_CLEAR: Unit ~> state_sel_e := <[ #2 ]>.

(* typedef enum logic [1:0] { *)
(*   ADD_RK_INIT, *)
(*   ADD_RK_ROUND, *)
(*   ADD_RK_FINAL *)
(* } add_rk_sel_e; *)
Definition add_rk_sel_e := Vector Bit 2.
Definition ADD_RK_INIT: Unit ~> add_rk_sel_e := <[ #0 ]>.
Definition ADD_RK_ROUND: Unit ~> add_rk_sel_e := <[ #1 ]>.
Definition ADD_RK_FINAL: Unit ~> add_rk_sel_e := <[ #2 ]>.

(* typedef enum logic { *)
(*   KEY_DEC_EXPAND, *)
(*   KEY_DEC_CLEAR *)
(* } key_dec_sel_e; *)
Definition key_dec_sel_e := Bit.
Definition KEY_DEC_EXPAND: Unit ~> key_dec_sel_e := <[ false' ]>.
Definition KEY_DEC_CLEAR: Unit ~> key_dec_sel_e := <[ true' ]>.

(* typedef enum logic [1:0] { *)
(*   KEY_WORDS_0123, *)
(*   KEY_WORDS_2345, *)
(*   KEY_WORDS_4567, *)
(*   KEY_WORDS_ZERO *)
(* } key_words_sel_e; *)
Definition key_words_sel_e := Vector Bit 2.
Definition KEY_WORDS_0123: Unit ~> key_words_sel_e := <[ #0 ]>.
Definition KEY_WORDS_2345: Unit ~> key_words_sel_e := <[ #1 ]>.
Definition KEY_WORDS_4567: Unit ~> key_words_sel_e := <[ #2 ]>.
Definition KEY_WORDS_ZERO: Unit ~> key_words_sel_e := <[ #3 ]>.

(* typedef enum logic { *)
(*   ROUND_KEY_DIRECT, *)
(*   ROUND_KEY_MIXED *)
(* } round_key_sel_e; *)
Definition round_key_sel_e := Bit.
Definition ROUND_KEY_DIRECT: Unit ~> round_key_sel_e := <[ false' ]>.
Definition ROUND_KEY_MIXED: Unit ~> round_key_sel_e := <[ true' ]>.

(* typedef enum logic [1:0] { *)
(*   KEY_FULL_ENC_INIT, *)
(*   KEY_FULL_DEC_INIT, *)
(*   KEY_FULL_ROUND, *)
(*   KEY_FULL_CLEAR *)
(* } key_full_sel_e; *)
Definition key_full_sel_e := Vector Bit 2.
Definition KEY_FULL_ENC_INIT: Unit ~> key_full_sel_e := <[ #0 ]>.
Definition KEY_FULL_DEC_INIT: Unit ~> key_full_sel_e := <[ #1 ]>.
Definition KEY_FULL_ROUND: Unit ~> key_full_sel_e := <[ #2 ]>.
Definition KEY_FULL_CLEAR: Unit ~> key_full_sel_e := <[ #3 ]>.

(* // Multiplication by {02} (i.e. x) on GF(2^8)
// with field generating polynomial {01}{1b} (9'h11b)
// Sometimes also denoted by xtime().
function automatic logic [7:0] aes_mul2(logic [7:0] in);
  logic [7:0] out;
  out[7] = in[6];
  out[6] = in[5];
  out[5] = in[4];
  out[4] = in[3] ^ in[7];
  out[3] = in[2] ^ in[7];
  out[2] = in[1];
  out[1] = in[0] ^ in[7];
  out[0] = in[7];
  return out;
endfunction *)
Definition aes_mul2:
  <<Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\ x => x[#7]
        :: (xor x[#0] x[#7])
        :: x[#1]
        :: (xor x[#2] x[#7])
        :: (xor x[#3] x[#7])
        :: x[#4]
        :: x[#5]
        :: x[#6] :: []
  ]>.

(* // Multiplication by {04} (i.e. x^2) on GF(2^8)
// with field generating polynomial {01}{1b} (9'h11b)
function automatic logic [7:0] aes_mul4(logic [7:0] in);
  return aes_mul2(aes_mul2(in));
endfunction *)
Definition aes_mul4:
  <<Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\ x => !aes_mul2 (!aes_mul2 x) ]>.

(* // Division by {02} (i.e. x) on GF(2^8)
// with field generating polynomial {01}{1b} (9'h11b)
// This is the inverse of aes_mul2() or xtime().
function automatic logic [7:0] aes_div2(logic [7:0] in);
  logic [7:0] out;
  out[7] = in[0];
  out[6] = in[7];
  out[5] = in[6];
  out[4] = in[5];
  out[3] = in[4] ^ in[0];
  out[2] = in[3] ^ in[0];
  out[1] = in[2];
  out[0] = in[1] ^ in[0];
  return out;
endfunction *)
Definition aes_div2:
  <<Vector Bit 8, Unit>> ~> (Vector Bit 8) :=
  <[\ x => (xor x[#1] x[#0])
        :: x[#2]
        :: (xor x[#3] x[#0])
        :: (xor x[#4] x[#0])
        :: x[#5]
        :: x[#6]
        :: x[#7]
        :: x[#0] :: []
  ]>.


(* function automatic logic [31:0] aes_circ_byte_shift(logic [31:0] in, logic [1:0] shift);
  logic [31:0] out;
  logic [31:0] s;
  s = {30'b0,shift};
  out = {in[8*((7-s)%4) +: 8], in[8*((6-s)%4) +: 8],
         in[8*((5-s)%4) +: 8], in[8*((4-s)%4) +: 8]};
  return out;
endfunction *)
Definition aes_circ_byte_shift:
  <<Vector (Vector Bit 8) 4, Vector Bit 2, Unit>> ~> (Vector (Vector Bit 8) 4) :=
  <[\input shift =>
      !(map3 <[\input shift seq =>
        let offset = seq - shift in
        input[offset]
      ]>
      )
      (!replicate input)
      (!replicate shift)
      !(seq 4)
  ]>.

(* function automatic logic [3:0][3:0][7:0] aes_transpose(logic [3:0][3:0][7:0] in);
  logic [3:0][3:0][7:0] transpose;
  transpose = '0;
  for (int j=0; j<4; j++) begin
    for (int i=0; i<4; i++) begin
      transpose[i][j] = in[j][i];
    end
  end
  return transpose;
endfunction *)
Fixpoint aes_transpose {n m}
  : <<Vector (Vector (Vector Bit 8) m) n, Unit>> ~>
      Vector (Vector (Vector Bit 8) n) m :=
match n with
| O => <[\_ => !replicate ([]) ]>
| S n' =>
  <[\mat =>
    let '(mat', vec) = unsnoc mat in
    !(map2 <[\vec x => snoc vec x ]>) (!aes_transpose mat') vec
    ]>
end.

Definition aes_mvm_acc
  :  <<Vector Bit 8, Vector Bit 8, Bit, Unit>> ~> (Vector Bit 8) :=
  <[\acc mat vec => acc ^ (mat & (!replicate vec)) ]>.

Definition aes_mvm:
  <<Vector Bit 8, Vector (Vector Bit 8) 8, Unit>> ~> (Vector Bit 8) :=
  <[\ vec_b mat_a =>
  let _1 = !aes_mvm_acc (#0) (mat_a[#0]) (vec_b[#7]) in
  let _2 = !aes_mvm_acc (_1) (mat_a[#1]) (vec_b[#6]) in
  let _3 = !aes_mvm_acc (_2) (mat_a[#2]) (vec_b[#5]) in
  let _4 = !aes_mvm_acc (_3) (mat_a[#3]) (vec_b[#4]) in
  let _5 = !aes_mvm_acc (_4) (mat_a[#4]) (vec_b[#3]) in
  let _6 = !aes_mvm_acc (_5) (mat_a[#5]) (vec_b[#2]) in
  let _7 = !aes_mvm_acc (_6) (mat_a[#6]) (vec_b[#1]) in
  let _8 = !aes_mvm_acc (_7) (mat_a[#7]) (vec_b[#0]) in
  _8
  ]>.
