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

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Cava.BitArithmetic.
Require Import AesSpec.Tests.Common.
Import ListNotations.
Local Open Scope string_scope.

Section FIPSC3.
  Definition fips_c3_forward : TestVector (key:=Vector.t bool 128) (state:=Vector.t bool 128) :=
    {| plaintext := Hex2Bv "0x00112233445566778899aabbccddeeff";
       round_ksch :=
         List.map Hex2Bv
                  [ (* round[ 0].k_sch *) "0x000102030405060708090a0b0c0d0e0f";
                  (* round[ 1].k_sch *) "0x101112131415161718191a1b1c1d1e1f";
                  (* round[ 2].k_sch *) "0xa573c29fa176c498a97fce93a572c09c";
                  (* round[ 3].k_sch *) "0x1651a8cd0244beda1a5da4c10640bade";
                  (* round[ 4].k_sch *) "0xae87dff00ff11b68a68ed5fb03fc1567";
                  (* round[ 5].k_sch *) "0x6de1f1486fa54f9275f8eb5373b8518d";
                  (* round[ 6].k_sch *) "0xc656827fc9a799176f294cec6cd5598b";
                  (* round[ 7].k_sch *) "0x3de23a75524775e727bf9eb45407cf39";
                  (* round[ 8].k_sch *) "0x0bdc905fc27b0948ad5245a4c1871c2f";
                  (* round[ 9].k_sch *) "0x45f5a66017b2d387300d4d33640a820a";
                  (* round[10].k_sch *) "0x7ccff71cbeb4fe5413e6bbf0d261a7df";
                  (* round[11].k_sch *) "0xf01afafee7a82979d7a5644ab3afe640";
                  (* round[12].k_sch *) "0x2541fe719bf500258813bbd55a721c0a";
                  (* round[13].k_sch *) "0x4e5a6699a9f24fe07e572baacdf8cdea";
                  (* round[14].k_sch *) "0x24fc79ccbf0979e9371ac23c6d68de36"
                  ];
       round_expected_states :=
         List.map
           (List.map (fun x => (fst x, Hex2Bv (snd x))))
           [
           (* Round 0 *)
           [ (* round[ 1].start *) (AddRoundKey, "0x00102030405060708090a0b0c0d0e0f0") ];
           (* Round 1 *)
           [ (* round[ 1].s_box *) (SubBytes,    "0x63cab7040953d051cd60e0e7ba70e18c");
             (* round[ 1].s_row *) (ShiftRows,   "0x6353e08c0960e104cd70b751bacad0e7");
             (* round[ 1].m_col *) (MixColumns,  "0x5f72641557f5bc92f7be3b291db9f91a");
             (* round[ 2].start *) (AddRoundKey, "0x4f63760643e0aa85efa7213201a4e705") ];
           (* Round 2 *)
           [ (* round[ 2].s_box *) (SubBytes,    "0x84fb386f1ae1ac97df5cfd237c49946b");
             (* round[ 2].s_row *) (ShiftRows,   "0x84e1fd6b1a5c946fdf4938977cfbac23");
             (* round[ 2].m_col *) (MixColumns,  "0xbd2a395d2b6ac438d192443e615da195");
             (* round[ 3].start *) (AddRoundKey, "0x1859fbc28a1c00a078ed8aadc42f6109") ];
           (* Round 3 *)
           [ (* round[ 3].s_box *) (SubBytes,    "0xadcb0f257e9c63e0bc557e951c15ef01");
             (* round[ 3].s_row *) (ShiftRows,   "0xad9c7e017e55ef25bc150fe01ccb6395");
             (* round[ 3].m_col *) (MixColumns,  "0x810dce0cc9db8172b3678c1e88a1b5bd");
             (* round[ 4].start *) (AddRoundKey, "0x975c66c1cb9f3fa8a93a28df8ee10f63") ];
           (* Round 4 *)
           [ (* round[ 4].s_box *) (SubBytes,    "0x884a33781fdb75c2d380349e19f876fb");
             (* round[ 4].s_row *) (ShiftRows,   "0x88db34fb1f807678d3f833c2194a759e");
             (* round[ 4].m_col *) (MixColumns,  "0xb2822d81abe6fb275faf103a078c0033");
             (* round[ 5].start *) (AddRoundKey, "0x1c05f271a417e04ff921c5c104701554") ];
           (* Round 5 *)
           [ (* round[ 5].s_box *) (SubBytes,    "0x9c6b89a349f0e18499fda678f2515920");
             (* round[ 5].s_row *) (ShiftRows,   "0x9cf0a62049fd59a399518984f26be178");
             (* round[ 5].m_col *) (MixColumns,  "0xaeb65ba974e0f822d73f567bdb64c877");
             (* round[ 6].start *) (AddRoundKey, "0xc357aae11b45b7b0a2c7bd28a8dc99fa") ];
           (* Round 6 *)
           [ (* round[ 6].s_box *) (SubBytes,    "0x2e5bacf8af6ea9e73ac67a34c286ee2d");
             (* round[ 6].s_row *) (ShiftRows,   "0x2e6e7a2dafc6eef83a86ace7c25ba934");
             (* round[ 6].m_col *) (MixColumns,  "0xb951c33c02e9bd29ae25cdb1efa08cc7");
             (* round[ 7].start *) (AddRoundKey, "0x7f074143cb4e243ec10c815d8375d54c") ];
           (* Round 7 *)
           [ (* round[ 7].s_box *) (SubBytes,    "0xd2c5831a1f2f36b278fe0c4cec9d0329");
             (* round[ 7].s_row *) (ShiftRows,   "0xd22f0c291ffe031a789d83b2ecc5364c");
             (* round[ 7].m_col *) (MixColumns,  "0xebb19e1c3ee7c9e87d7535e9ed6b9144");
             (* round[ 8].start *) (AddRoundKey, "0xd653a4696ca0bc0f5acaab5db96c5e7d") ];
           (* Round 8 *)
           [ (* round[ 8].s_box *) (SubBytes,    "0xf6ed49f950e06576be74624c565058ff");
             (* round[ 8].s_row *) (ShiftRows,   "0xf6e062ff507458f9be50497656ed654c");
             (* round[ 8].m_col *) (MixColumns,  "0x5174c8669da98435a8b3e62ca974a5ea");
             (* round[ 9].start *) (AddRoundKey, "0x5aa858395fd28d7d05e1a38868f3b9c5") ];
           (* Round 9 *)
           [ (* round[ 9].s_box *) (SubBytes,    "0xbec26a12cfb55dff6bf80ac4450d56a6");
             (* round[ 9].s_row *) (ShiftRows,   "0xbeb50aa6cff856126b0d6aff45c25dc4");
             (* round[ 9].m_col *) (MixColumns,  "0x0f77ee31d2ccadc05430a83f4ef96ac3");
             (* round[10].start *) (AddRoundKey, "0x4a824851c57e7e47643de50c2af3e8c9") ];
           (* Round 10 *)
           [ (* round[10].s_box *) (SubBytes,    "0xd61352d1a6f3f3a04327d9fee50d9bdd");
             (* round[10].s_row *) (ShiftRows,   "0xd6f3d9dda6279bd1430d52a0e513f3fe");
             (* round[10].m_col *) (MixColumns,  "0xbd86f0ea748fc4f4630f11c1e9331233");
             (* round[11].start *) (AddRoundKey, "0xc14907f6ca3b3aa070e9aa313b52b5ec") ];
           (* Round 11 *)
           [ (* round[11].s_box *) (SubBytes,    "0x783bc54274e280e0511eacc7e200d5ce");
             (* round[11].s_row *) (ShiftRows,   "0x78e2acce741ed5425100c5e0e23b80c7");
             (* round[11].m_col *) (MixColumns,  "0xaf8690415d6e1dd387e5fbedd5c89013");
             (* round[12].start *) (AddRoundKey, "0x5f9c6abfbac634aa50409fa766677653") ];
           (* Round 12 *)
           [ (* round[12].s_box *) (SubBytes,    "0xcfde0208f4b418ac5309db5c338538ed");
             (* round[12].s_row *) (ShiftRows,   "0xcfb4dbedf4093808538502ac33de185c");
             (* round[12].m_col *) (MixColumns,  "0x7427fae4d8a695269ce83d315be0392b");
             (* round[13].start *) (AddRoundKey, "0x516604954353950314fb86e401922521") ];
           (* Round 13 *)
           [ (* round[13].s_box *) (SubBytes,    "0xd133f22a1aed2a7bfa0f44697c4f3ffd");
             (* round[13].s_row *) (ShiftRows,   "0xd1ed44fd1a0f3f2afa4ff27b7c332a69");
             (* round[13].m_col *) (MixColumns,  "0x2c21a820306f154ab712c75eee0da04f");
             (* round[14].start *) (AddRoundKey, "0x627bceb9999d5aaac945ecf423f56da5") ];
           (* Round 14 *)
           [ (* round[14].s_box *) (SubBytes,    "0xaa218b56ee5ebeacdd6ecebf26e63c06");
             (* round[14].s_row *) (ShiftRows,   "0xaa5ece06ee6e3c56dde68bac2621bebf");
             (* round[14].output*) (AddRoundKey, "0x8ea2b7ca516745bfeafc49904b496089") ]
           ];
    |}.
End FIPSC3.

(*
Compute pretty_print_test_vector Bv2Hex Bv2Hex fips_c3_forward.
*)
