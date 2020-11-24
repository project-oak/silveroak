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

  Definition fips_c3_equivalent_inverse
    : TestVector (key:=Vector.t bool 128) (state:=Vector.t bool 128) :=
    {| plaintext := Hex2Bv "0x8ea2b7ca516745bfeafc49904b496089";
       round_ksch :=
         List.map Hex2Bv
                  [ (* round[ 0].ik_sch *) "0x24fc79ccbf0979e9371ac23c6d68de36";
                  (* round[ 1].ik_sch *) "0x34f1d1ffbfceaa2ffce9e25f2558016e";
                  (* round[ 2].ik_sch *) "0x5e1648eb384c350a7571b746dc80e684";
                  (* round[ 3].ik_sch *) "0xc8a305808b3f7bd043274870d9b1e331";
                  (* round[ 4].ik_sch *) "0xb5708e13665a7de14d3d824ca9f151c2";
                  (* round[ 5].ik_sch *) "0x74da7ba3439c7e50c81833a09a96ab41";
                  (* round[ 6].ik_sch *) "0x3ca69715d32af3f22b67ffade4ccd38e";
                  (* round[ 7].ik_sch *) "0xf85fc4f3374605f38b844df0528e98e1";
                  (* round[ 8].ik_sch *) "0xde69409aef8c64e7f84d0c5fcfab2c23";
                  (* round[ 9].ik_sch *) "0xaed55816cf19c100bcc24803d90ad511";
                  (* round[10].ik_sch *) "0x15c668bd31e5247d17c168b837e6207c";
                  (* round[11].ik_sch *) "0x7fd7850f61cc991673db890365c89d12";
                  (* round[12].ik_sch *) "0x2a2840c924234cc026244cc5202748c4";
                  (* round[13].ik_sch *) "0x1a1f181d1e1b1c191217101516131411";
                  (* round[14].ik_sch *) "0x000102030405060708090a0b0c0d0e0f"
                  ];
       round_expected_states :=
         List.map
           (List.map (fun x => (fst x, Hex2Bv (snd x))))
           [
           (* Round 0 *)
           [ (* round[ 1].istart *) (AddRoundKey,   "0xaa5ece06ee6e3c56dde68bac2621bebf") ];
           (* Round 1 *)
           [ (* round[ 1].is_box *) (InvSubBytes,   "0x629deca599456db9c9f5ceaa237b5af4");
             (* round[ 1].is_row *) (InvShiftRows,  "0x627bceb9999d5aaac945ecf423f56da5");
             (* round[ 1].im_col *) (InvMixColumns, "0xe51c9502a5c1950506a61024596b2b07");
             (* round[ 2].istart *) (AddRoundKey,   "0xd1ed44fd1a0f3f2afa4ff27b7c332a69") ];
           (* Round 2 *)
           [ (* round[ 2].is_box *) (InvSubBytes,   "0x5153862143fb259514920403016695e4");
             (* round[ 2].is_row *) (InvShiftRows,  "0x516604954353950314fb86e401922521");
             (* round[ 2].im_col *) (InvMixColumns, "0x91a29306cc450d0226f4b5eaef5efed8");
             (* round[ 3].istart *) (AddRoundKey,   "0xcfb4dbedf4093808538502ac33de185c") ];
           (* Round 3 *)
           [ (* round[ 3].is_box *) (InvSubBytes,   "0x5fc69f53ba4076bf50676aaa669c34a7");
             (* round[ 3].is_row *) (InvShiftRows,  "0x5f9c6abfbac634aa50409fa766677653");
             (* round[ 3].im_col *) (InvMixColumns, "0xb041a94eff21ae9212278d903b8a63f6");
             (* round[ 4].istart *) (AddRoundKey,   "0x78e2acce741ed5425100c5e0e23b80c7") ];
           (* Round 4 *)
           [ (* round[ 4].is_box *) (InvSubBytes,   "0xc13baaeccae9b5f6705207a03b493a31");
             (* round[ 4].is_row *) (InvShiftRows,  "0xc14907f6ca3b3aa070e9aa313b52b5ec");
             (* round[ 4].im_col *) (InvMixColumns, "0x638357cec07de6300e30d0ec4ce2a23c");
             (* round[ 5].istart *) (AddRoundKey,   "0xd6f3d9dda6279bd1430d52a0e513f3fe") ];
           (* Round 5 *)
           [ (* round[ 5].is_box *) (InvSubBytes,   "0x4a7ee5c9c53de85164f348472a827e0c");
             (* round[ 5].is_row *) (InvShiftRows,  "0x4a824851c57e7e47643de50c2af3e8c9");
             (* round[ 5].im_col *) (InvMixColumns, "0xca6f71058c642842a315595fdf54f685");
             (* round[ 6].istart *) (AddRoundKey,   "0xbeb50aa6cff856126b0d6aff45c25dc4") ];
           (* Round 6 *)
           [ (* round[ 6].is_box *) (InvSubBytes,   "0x5ad2a3c55fe1b93905f3587d68a88d88");
             (* round[ 6].is_row *) (InvShiftRows,  "0x5aa858395fd28d7d05e1a38868f3b9c5");
             (* round[ 6].im_col *) (InvMixColumns, "0xca46f5ea835eab0b9537b6dbb221b6c2");
             (* round[ 7].istart *) (AddRoundKey,   "0xf6e062ff507458f9be50497656ed654c") ];
           (* Round 7 *)
           [ (* round[ 7].is_box *) (InvSubBytes,   "0xd6a0ab7d6cca5e695a6ca40fb953bc5d");
             (* round[ 7].is_row *) (InvShiftRows,  "0xd653a4696ca0bc0f5acaab5db96c5e7d");
             (* round[ 7].im_col *) (InvMixColumns, "0x2a70c8da28b806e9f319ce42be4baead");
             (* round[ 8].istart *) (AddRoundKey,   "0xd22f0c291ffe031a789d83b2ecc5364c") ];
           (* Round 8 *)
           [ (* round[ 8].is_box *) (InvSubBytes,   "0x7f4e814ccb0cd543c175413e8307245d");
             (* round[ 8].is_row *) (InvShiftRows,  "0x7f074143cb4e243ec10c815d8375d54c");
             (* round[ 8].im_col *) (InvMixColumns, "0xf0073ab7404a8a1fc2cba0b80df08517");
             (* round[ 9].istart *) (AddRoundKey,   "0x2e6e7a2dafc6eef83a86ace7c25ba934") ];
           (* Round 9 *)
           [ (* round[ 9].is_box *) (InvSubBytes,   "0xc345bdfa1bc799e1a2dcaab0a857b728");
             (* round[ 9].is_row *) (InvShiftRows,  "0xc357aae11b45b7b0a2c7bd28a8dc99fa");
             (* round[ 9].im_col *) (InvMixColumns, "0x3225fe3686e498a32593c1872b613469");
             (* round[10].istart *) (AddRoundKey,   "0x9cf0a62049fd59a399518984f26be178") ];
           (* Round 10 *)
           [ (* round[10].is_box *) (InvSubBytes,   "0x1c17c554a4211571f970f24f0405e0c1");
             (* round[10].is_row *) (InvShiftRows,  "0x1c05f271a417e04ff921c5c104701554");
             (* round[10].im_col *) (InvMixColumns, "0x9d1d5c462e655205c4395b7a2eac55e2");
             (* round[11].istart *) (AddRoundKey,   "0x88db34fb1f807678d3f833c2194a759e") ];
           (* Round 11 *)
           [ (* round[11].is_box *) (InvSubBytes,   "0x979f2863cb3a0fc1a9e166a88e5c3fdf");
             (* round[11].is_row *) (InvShiftRows,  "0x975c66c1cb9f3fa8a93a28df8ee10f63");
             (* round[11].im_col *) (InvMixColumns, "0xd24bfb0e1f997633cfce86e37903fe87");
             (* round[12].istart *) (AddRoundKey,   "0xad9c7e017e55ef25bc150fe01ccb6395") ];
           (* Round 12 *)
           [ (* round[12].is_box *) (InvSubBytes,   "0x181c8a098aed61c2782ffba0c45900ad");
             (* round[12].is_row *) (InvShiftRows,  "0x1859fbc28a1c00a078ed8aadc42f6109");
             (* round[12].im_col *) (InvMixColumns, "0xaec9bda23e7fd8aff96d74525cdce4e7");
             (* round[13].istart *) (AddRoundKey,   "0x84e1fd6b1a5c946fdf4938977cfbac23") ];
           (* Round 13 *)
           [ (* round[13].is_box *) (InvSubBytes,   "0x4fe0210543a7e706efa476850163aa32");
             (* round[13].is_row *) (InvShiftRows,  "0x4f63760643e0aa85efa7213201a4e705");
             (* round[13].im_col *) (InvMixColumns, "0x794cf891177bfd1ddf67a744acd9c4f6");
             (* round[14].istart *) (AddRoundKey,   "0x6353e08c0960e104cd70b751bacad0e7") ];
           (* Round 14 *)
           [ (* round[14].is_box *) (InvSubBytes,   "0x0050a0f04090e03080d02070c01060b0");
             (* round[14].is_row *) (InvShiftRows,  "0x00102030405060708090a0b0c0d0e0f0");
             (* round[14].ioutput*) (AddRoundKey,   "0x00112233445566778899aabbccddeeff") ]
           ];
    |}.
End FIPSC3.

(*
Compute pretty_print_test_vector Bv2Hex Bv2Hex fips_c3_forward.
*)
