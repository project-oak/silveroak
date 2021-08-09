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

Require Import Coq.NArith.NArith.
Local Open Scope N_scope.

Record hmac_test_vector :=
  { lK : nat;
    ldata : nat;
    K : N;
    data : N;
    expected_output : N }.

Record hmac_step_by_step_test : Type :=
  { test :> hmac_test_vector;
    expected_padded_key : N;
    (* K ^ ipad *)
    expected_xor_K_ipad : N;
    (* K ^ opad *)
    expected_xor_K_opad : N;
    (* inner hash result *)
    expected_inner : N;
  }.

(**** Test vectors from
      https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/HMAC_SHA256.pdf *)

Definition test1 : hmac_step_by_step_test :=
  {| test :=
       {| lK := 64;
          ldata := 34;
          K := 0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F303132333435363738393A3B3C3D3E3F;
          data := 0x53616D706C65206D65737361676520666F72206B65796C656E3D626C6F636B6C656E;
          expected_output := 0x8BB9A1DB9806F20DF7F77B82138C7914D174D59E13DC4D0169C9057B133E1D62 |};
     expected_padded_key := 0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F303132333435363738393A3B3C3D3E3F;
     expected_xor_K_ipad := 0x36373435323330313E3F3C3D3A3B383926272425222320212E2F2C2D2A2B282916171415121310111E1F1C1D1A1B181906070405020300010E0F0C0D0A0B0809;
     expected_xor_K_opad := 0x5C5D5E5F58595A5B54555657505152534C4D4E4F48494A4B44454647404142437C7D7E7F78797A7B74757677707172736C6D6E6F68696A6B6465666760616263;
     expected_inner := 0xC0918E14C43562B910DB4B8101CF8812C3DA2783C670BFF34D88B3B88E731716 |}.

Definition test2 : hmac_step_by_step_test :=
  {| test :=
       {| lK := 32;
          ldata := 34;
          K := 0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F;
          data := 0x53616D706C65206D65737361676520666F72206B65796C656E3C626C6F636B6C656E;
          expected_output := 0xA28CF43130EE696A98F14A37678B56BCFCBDD9E5CF69717FECF5480F0EBDF790 |};
     expected_padded_key := 0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F0000000000000000000000000000000000000000000000000000000000000000;
     expected_xor_K_ipad := 0x36373435323330313E3F3C3D3A3B383926272425222320212E2F2C2D2A2B28293636363636363636363636363636363636363636363636363636363636363636;
     expected_xor_K_opad := 0x5C5D5E5F58595A5B54555657505152534C4D4E4F48494A4B44454647404142435C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C;
     expected_inner := 0xB3C52720B330A1D3C4D8B594A9A73D207ED02EE5078A4A422258BD6514070A5F |}.

Definition test3 : hmac_step_by_step_test :=
  {| test :=
       {| lK := 100;
          ldata := 34;
          K := 0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F202122232425262728292A2B2C2D2E2F303132333435363738393A3B3C3D3E3F404142434445464748494A4B4C4D4E4F505152535455565758595A5B5C5D5E5F60616263;
          data := 0x53616D706C65206D65737361676520666F72206B65796C656E3D626C6F636B6C656E;
          expected_output := 0xBDCCB6C72DDEADB500AE768386CB38CC41C63DBB0878DDB9C7A38A431B78378D |};
     expected_padded_key := 0xBCE0AFF19CF5AA6A7469A30D61D04E4376E4BBF6381052EE9E7F33925C954D520000000000000000000000000000000000000000000000000000000000000000;
     expected_xor_K_ipad := 0x8AD699C7AAC39C5C425F953B57E6787540D28DC00E2664D8A84905A46AA37B643636363636363636363636363636363636363636363636363636363636363636;
     expected_xor_K_opad := 0xE0BCF3ADC0A9F6362835FF513D8C121F2AB8E7AA644C0EB2C2236FCE00C9110E5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C5C;
     expected_inner := 0x1E0DFB0CBB61E9F060769E9DF57501292426F0DB58194BC85BC63DAC4670C2C1 |}.
