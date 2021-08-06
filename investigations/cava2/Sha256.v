(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Coq.Strings.String.
Require Import Coq.Strings.HexString.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Primitives.

Import ListNotations.
Import ExprNotations.
Import PrimitiveNotations.

Local Open Scope string_scope.
Local Open Scope N.

Section Var.
  Context {var : tvar}.

  Definition sha_round := BitVec 6.
  Definition sha_word := BitVec 32.
  Definition sha_block := Vec sha_word 16.
  Definition sha_digest := Vec sha_word 8.

  (* SHA-256 message padding *)
  Definition sha256_padder : Circuit _ [Bit; BitVec 32; Bit; Bit] (sha_block ** Bit) := {{
    fun data_valid data finish clear =>
    (* TODO *)
    `circuit_hole`
  }}.

  (* SHA-256 initial digest *)
  Definition sha256_initial_digest : denote_type sha_digest :=
    List.map (HexString.to_N)
    [ "0x6a09e667" ; "0xbb67ae85" ; "0x3c6ef372" ; "0xa54ff53a"
    ; "0x510e527f" ; "0x9b05688c" ; "0x1f83d9ab" ; "0x5be0cd19" ].

  (* SHA-256 round constants *)
  Definition sha256_round_constants : Circuit [] [sha_round] sha_word := {{
    fun i =>
    let k :=
    `
    Constant (
    List.map (HexString.to_N)
    [ "0x428a2f98"; "0x71374491"; "0xb5c0fbcf"; "0xe9b5dba5"
    ; "0x3956c25b"; "0x59f111f1"; "0x923f82a4"; "0xab1c5ed5"
    ; "0xd807aa98"; "0x12835b01"; "0x243185be"; "0x550c7dc3"
    ; "0x72be5d74"; "0x80deb1fe"; "0x9bdc06a7"; "0xc19bf174"
    ; "0xe49b69c1"; "0xefbe4786"; "0x0fc19dc6"; "0x240ca1cc"
    ; "0x2de92c6f"; "0x4a7484aa"; "0x5cb0a9dc"; "0x76f988da"
    ; "0x983e5152"; "0xa831c66d"; "0xb00327c8"; "0xbf597fc7"
    ; "0xc6e00bf3"; "0xd5a79147"; "0x06ca6351"; "0x14292967"
    ; "0x27b70a85"; "0x2e1b2138"; "0x4d2c6dfc"; "0x53380d13"
    ; "0x650a7354"; "0x766a0abb"; "0x81c2c92e"; "0x92722c85"
    ; "0xa2bfe8a1"; "0xa81a664b"; "0xc24b8b70"; "0xc76c51a3"
    ; "0xd192e819"; "0xd6990624"; "0xf40e3585"; "0x106aa070"
    ; "0x19a4c116"; "0x1e376c08"; "0x2748774c"; "0x34b0bcb5"
    ; "0x391c0cb3"; "0x4ed8aa4a"; "0x5b9cca4f"; "0x682e6ff3"
    ; "0x748f82ee"; "0x78a5636f"; "0x84c87814"; "0x8cc70208"
    ; "0x90befffa"; "0xa4506ceb"; "0xbef9a3f7"; "0xc67178f2" ] : denote_type (Vec sha_word 64)
    )
    ` in
    `index` k i
  }}.

  (* SHA-256 message schedule update *)
  Definition sha256_message_schedule_update : Circuit _ [sha_word; sha_word; sha_word; sha_word] sha_word := {{
    fun w0 w1 w9 w14 =>
    let sum0 := (w1 >>> `7`) ^ (w1 >>> `18`) ^ (w1 >> `3`) in
    let sum1 := (w14 >>> `17`) ^ (w14 >>> `19`) ^ (w14 >> `10`) in
    w0 + sum0 + w9 + sum1
  }}%nat.

  (* SHA-256 compression function *)
  Program
  Definition sha256_compress : Circuit []%circuit_type [sha_digest; sha_word; sha_word]%circuit_type sha_digest := {{
    fun current_digest k w =>
    let '( a', b', c', d', e', f', g'; h' ) := `vec_as_tuple (n:=7)` current_digest in

    let s1 := (e' >>> `6`) ^ (e' >>> `11`) ^ (e' >>> `25`) in
    let ch := (e' & f') ^ (e' & g') in
    let temp1 := (h' + s1 + ch + k + w) in
    let s0 := (a' >>> `2`) ^ (a' >>> `13`) ^ (a' >>> `22`) in
    let maj := (a' & b') ^ (a' & c') ^ (b' & c') in
    let temp2 := s0 + maj in


    (temp1 + temp2) :> a' :> b' :> c' :> (d' + temp1) :> e' :> f' :> g' :> []
  }}%nat.

  (* SHA-256 core *)
  Definition sha256_inner : Circuit _ [sha_block; Bit; sha_digest] (sha_digest ** Bit) :=
    {{
    fun block block_valid initial_hash =>

    let/delay '(current_digest, message_schedule, done; round) :=

      let inc_round := !done in
      let start := (* done && *) block_valid in

      let k_i := `sha256_round_constants` round in
      let '(w0,w1, _, _, _, _, _, _
           , _,w9, _, _, _, _,w14;_ ) := `vec_as_tuple (n:=15)` message_schedule in
      let update_schedule := round >= `K 16` in
      let w16 :=
        if update_schedule
        then `sha256_message_schedule_update` w0 w1 w9 w14
        else `index` message_schedule round in
      let w :=
        if update_schedule
        then message_schedule <<+ w16
        else message_schedule in

      let next_digest := `sha256_compress` current_digest k_i w0 in

      let round := if inc_round then round + `K 1` else round in
      let done := (round == `K 63`) || done in

      if start
      then (initial_hash, block, `Constant ((false, 0):denote_type (Bit**sha_round))`)
      else (next_digest, w, done, round)

      initially ((sha256_initial_digest, (repeat 0 16, (false, 0)))
        : denote_type (sha_digest ** Vec sha_word 16 ** Bit ** sha_round )) in

    (current_digest, done)

  }}.

End Var.

(* Section SanityCheck. *)
(*   Require Import Cava.Semantics. *)
(*   Time Compute step sha256_message_schedule_update tt (0,(3,(6,(9,tt)))). *)
(*   Open Scope list_scope. *)
(*   Time Compute step sha256_compress tt ([1;2;3;4;5;7;8;9],(1,(2,tt))). *)
(* End SanityCheck. *)
