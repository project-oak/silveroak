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
From Arrow Require Import Category Arrow.
From Cava Require Import Arrow.ArrowExport BitArithmetic.

From ArrowExamples Require Import Combinators.

Import KappaNotation.
Open Scope kind_scope.

Notation "|^ x" :=
  (App (Morphism (foldl1 <[\a b => xor a b]>)) x)
  (in custom expr at level 5, no associativity) : kappa_scope.
Notation "x && y" :=
  (App (App And x) y)
  (in custom expr at level 6, left associativity) : kappa_scope.
Notation "x & y" :=
  (App (App (Morphism (map2 <[\a b => and a b]>)) x) y)
  (in custom expr at level 6, left associativity) : kappa_scope.
Notation "x ^ y" :=
  (App (App (Morphism (map2 <[\a b => xor a b]>)) x) y)
  (in custom expr at level 6, left associativity) : kappa_scope.
Notation "'if' i 'then' t 'else' e" :=
  (App (App (App (Morphism mux_bitvec) i) t) e)
  (in custom expr at level 5, left associativity) : kappa_scope.
Notation "x == y" :=
  (App (App (Morphism equality) x) y)
  (in custom expr at level 6, left associativity) : kappa_scope.

(* typedef enum logic {
  CIPH_FWD = 1'b0,
  CIPH_INV = 1'b1
} ciph_op_e; *)
Definition CIPH_FWD: forall cava: Cava, Unit ~> Bit := <[ false ]>.
Definition CIPH_INV: forall cava: Cava, Unit ~> Bit := <[ true ]>.

Inductive SboxImpl := 
(* | SboxLut *)
| SboxCanright
(* | SboxCanrightMasked *)
| SboxCanrightMaskedNoReuse.

Definition aes_mvm_acc
  : forall cava: Cava, <<Vector Bit 8, Vector Bit 8, Bit, Unit>> ~> (Vector Bit 8) :=
  <[\acc mat vec => acc ^ (mat & (!replicate vec)) ]>.

Definition aes_mvm: forall cava: Cava,
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


(* function automatic logic [31:0] aes_circ_byte_shift(logic [31:0] in, logic [1:0] shift);
  logic [31:0] out;
  logic [31:0] s;
  s = {30'b0,shift};
  out = {in[8*((7-s)%4) +: 8], in[8*((6-s)%4) +: 8],
         in[8*((5-s)%4) +: 8], in[8*((4-s)%4) +: 8]};
  return out;
endfunction *)
Definition aes_circ_byte_shift: forall cava: Cava,
  <<Vector Bit 32, Vector Bit 2, Unit>> ~> (Vector Bit 32) :=
  <[\input shift =>
    let as_bytes = !(@reshape 4 8 Bit) input in
    let transformed = 
      !(map3 <[\in_ shift seq => 
      (* in_[8*((4-shift)%4) +: 8]
      in_[8*((5-shift)%4) +: 8] ::
      in_[8*((6-shift)%4) +: 8] :: 
      in_[8*((7-shift)%4) +: 8] :: [] *)
      #0 ]> (* todo *)
      ) as_bytes (!replicate shift) !(@seq _ 0 4) in
    !(@flatten 4 8 _) transformed
  ]>.


