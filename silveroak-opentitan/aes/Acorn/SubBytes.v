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

Require Import Coq.Vectors.Vector.
Require Import Coq.NArith.Ndigits.

Require Import ExtLib.Structures.Monads.

Require Import Cava.VectorUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.BitArithmetic.
Require Import Cava.Lib.BitVectorOps.
Require Import AcornAes.Common.
Require Import AesSpec.StateTypeConversions.
Require Import AesSpec.Tests.CipherTest.
Require Import AesSpec.Tests.Common.
Import Common.Notations.
Import VectorNotations.
Import StateTypeConversions.LittleEndian.

Section SboxLut.
  Definition sbox_fwd : t nat _ :=
    [ 99; 124; 119; 123; 242; 107; 111; 197;
      48; 1; 103; 43; 254; 215; 171; 118;

      202; 130; 201; 125; 250; 89; 71; 240;
      173; 212; 162; 175; 156; 164; 114; 192;

      183; 253; 147; 38; 54; 63; 247; 204;
      52; 165; 229; 241; 113; 216; 49; 21;

      4; 199; 35; 195; 24; 150; 5; 154;
      7; 18; 128; 226; 235; 39; 178; 117;

      9; 131; 44; 26; 27; 110; 90; 160;
      82; 59; 214; 179; 41; 227; 47; 132;

      83; 209; 0; 237; 32; 252; 177; 91;
      106; 203; 190; 57; 74; 76; 88; 207;

      208; 239; 170; 251; 67; 77; 51; 133;
      69; 249; 2; 127; 80; 60; 159; 168;

      81; 163; 64; 143; 146; 157; 56; 245;
      188; 182; 218; 33; 16; 255; 243; 210;

      205; 12; 19; 236; 95; 151; 68; 23;
      196; 167; 126; 61; 100; 93; 25; 115;

      96; 129; 79; 220; 34; 42; 144; 136;
      70; 238; 184; 20; 222; 94; 11; 219;

      224; 50; 58; 10; 73; 6; 36; 92;
      194; 211; 172; 98; 145; 149; 228; 121;

      231; 200; 55; 109; 141; 213; 78; 169;
      108; 86; 244; 234; 101; 122; 174; 8;

      186; 120; 37; 46; 28; 166; 180; 198;
      232; 221; 116; 31; 75; 189; 139; 138;

      112; 62; 181; 102; 72; 3; 246; 14;
      97; 53; 87; 185; 134; 193; 29; 158;

      225; 248; 152; 17; 105; 217; 142; 148;
      155; 30; 135; 233; 206; 85; 40; 223;

      140; 161; 137; 13; 191; 230; 66; 104;
      65; 153; 45; 15; 176; 84; 187; 22 ].

  Definition sbox_inv : t nat _ :=
    [ 82; 9; 106; 213; 48; 54; 165; 56;
      191; 64; 163; 158; 129; 243; 215; 251;

      124; 227; 57; 130; 155; 47; 255; 135;
      52; 142; 67; 68; 196; 222; 233; 203;

      84; 123; 148; 50; 166; 194; 35; 61;
      238; 76; 149; 11; 66; 250; 195; 78;

      8; 46; 161; 102; 40; 217; 36; 178;
      118; 91; 162; 73; 109; 139; 209; 37;

      114; 248; 246; 100; 134; 104; 152; 22;
      212; 164; 92; 204; 93; 101; 182; 146;

      108; 112; 72; 80; 253; 237; 185; 218;
      94; 21; 70; 87; 167; 141; 157; 132;

      144; 216; 171; 0; 140; 188; 211; 10;
      247; 228; 88; 5; 184; 179; 69; 6;

      208; 44; 30; 143; 202; 63; 15; 2;
      193; 175; 189; 3; 1; 19; 138; 107;

      58; 145; 17; 65; 79; 103; 220; 234;
      151; 242; 207; 206; 240; 180; 230; 115;

      150; 172; 116; 34; 231; 173; 53; 133;
      226; 249; 55; 232; 28; 117; 223; 110;

      71; 241; 26; 113; 29; 41; 197; 137;
      111; 183; 98; 14; 170; 24; 190; 27;

      252; 86; 62; 75; 198; 210; 121; 32;
      154; 219; 192; 254; 120; 205; 90; 244;

      31; 221; 168; 51; 136; 7; 199; 49;
      177; 18; 16; 89; 39; 128; 236; 95;

      96; 81; 127; 169; 25; 181; 74; 13;
      45; 229; 122; 159; 147; 201; 156; 239;

      160; 224; 59; 77; 174; 42; 245; 176;
      200; 235; 187; 60; 131; 83; 153; 97;

      23; 43; 4; 126; 186; 119; 214; 38;
      225; 105; 20; 99; 85; 33; 12; 125 ].
End SboxLut.

Section WithCava.
  Context {signal} {semantics : Cava signal}.
  Context {monad: Monad cava}.

  Definition bitvec_to_signal {n : nat} (lut : t bool n) : signal (Vec Bit n) :=
    unpeel (map constant lut).

  Definition bitvecvec_to_signal {a b : nat} (lut : t (t bool b) a) : signal (Vec (Vec Bit b) a) :=
    unpeel (map bitvec_to_signal lut).

  Definition natvec_to_signal_sized {n : nat} (size : nat) (lut : t nat n) : signal (Vec (Vec Bit size) n) :=
    bitvecvec_to_signal (map (nat_to_bitvec_sized size) lut).

  Definition sbox_fwd_lut := natvec_to_signal_sized 8 sbox_fwd.
  Definition sbox_inv_lut := natvec_to_signal_sized 8 sbox_inv.

  Definition state_map (f : signal (Vec Bit 8) -> signal (Vec Bit 8)) (s : signal state) : signal state :=
    unpeel (map unpeel (map (fun t => map f t) (map peel (peel s)))).

  Definition sub_bytes (is_decrypt : signal Bit) (b : signal state)
    : cava (signal state) :=
    let encrypted := state_map (fun i => indexAt sbox_fwd_lut i) b in
    let decrypted := state_map (fun i => indexAt sbox_inv_lut i) b in
    ret (pairSel is_decrypt (mkpair encrypted decrypted)).
End WithCava.

(* Run test as a quick-feedback check *)
Import List.ListNotations.
Require Import Coq.Strings.String.
Goal
  (let signal := combType in
   (* convert between flat-vector representation and state type *)
   let to_state : Vector.t bool 128 -> signal state :=
       fun st => map reshape (to_cols_bits st) in
   let from_state : signal state -> Vector.t bool 128 :=
       fun st => from_cols_bits (map flatten st) in
   (* run encrypt test with this version of add_round_key plugged in *)
   aes_test_encrypt Hex
                    (fun step key =>
                       match step with
                       | SubBytes => fun st =>
                           let input := to_state st in
                           let output := unIdent (sub_bytes [false]%list [input]%list) in
                           from_state (List.hd (defaultCombValue _) output)
                       | InvSubBytes => fun st =>
                           let input := to_state st in
                           let output := unIdent (sub_bytes [true]%list [input]%list) in
                           from_state (List.hd (defaultCombValue _) output)
                       | _ => aes_impl step key
                       end) = Success).
Proof. vm_compute. reflexivity. Qed.

