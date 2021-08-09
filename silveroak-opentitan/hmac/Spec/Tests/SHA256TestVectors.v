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

Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Cava.Util.String.
Import ListNotations.
Local Open Scope N_scope.

Record sha256_test_vector :=
  { msg : string;
    msg_N := string_to_N msg;
    l := N.of_nat (String.length msg * 8);
    expected_digest : N }.

Record sha256_step_by_step_test : Type :=
  { test :> sha256_test_vector;
    expected_padded_msg : N;
    (* first 16 blocks of W for each round *)
    expected_blocks : list (list N);
    (* H at the end of each round *)
    expected_intermediate_digests : list (list N) }.

(**** Test vectors from
      https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf ****)

Definition test1 : sha256_step_by_step_test :=
  {| test :=
       {| msg := "abc";
          expected_digest := 0xBA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD |};
     expected_padded_msg := 0x61626380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018;
     expected_blocks :=
       [ (* first 16 blocks of W for i=0 *)
         [ 0x61626380
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000000
           ; 0x00000018 ] ];
     expected_intermediate_digests :=
       [ (* H[0] - H[7] after round 0 *)
         [ 0xBA7816BF
           ; 0x8F01CFEA
           ; 0x414140DE
           ; 0x5DAE2223
           ; 0xB00361A3
           ; 0x96177A9C
           ; 0xB410FF61
           ; 0xF20015AD ] ];
  |}.

Definition test2 : sha256_step_by_step_test :=
  {| test :=
       {| msg := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
          expected_digest := 0x248D6A61D20638B8E5C026930C3E6039A33CE45964FF2167F6ECEDD419DB06C1 |};
     expected_padded_msg := 0x6162636462636465636465666465666765666768666768696768696A68696A6B696A6B6C6A6B6C6D6B6C6D6E6C6D6E6F6D6E6F706E6F70718000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001C0;
     expected_blocks :=
       [ (* first 16 blocks of W for i=0 *)
         [ 0x61626364
           ; 0x62636465
           ; 0x63646566
           ; 0x64656667
           ; 0x65666768
           ; 0x66676869
           ; 0x6768696A
           ; 0x68696A6B
           ; 0x696A6B6C
           ; 0x6A6B6C6D
           ; 0x6B6C6D6E
           ; 0x6C6D6E6F
           ; 0x6D6E6F70
           ; 0x6E6F7071
           ; 0x80000000
           ; 0x00000000];
       (* first 16 blocks of W for i=1 *)
       [ 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x00000000
         ; 0x000001C0 ] ];
     expected_intermediate_digests :=
       [ (* H[0] - H[7] after round 0 *)
         [ 0x85E655D6
           ; 0x417A1795
           ; 0x3363376A
           ; 0x624CDE5C
           ; 0x76E09589
           ; 0xCAC5F811
           ; 0xCC4B32C1
           ; 0xF20E533A ];
       (* H[0] - H[7] after round 1 *)
       [ 0x248D6A61
         ; 0xD20638B8
         ; 0xE5C02693
         ; 0x0C3E6039
         ; 0xA33CE459
         ; 0x64FF2167
         ; 0xF6ECEDD4
         ; 0x19DB06C1 ] ];
  |}.
