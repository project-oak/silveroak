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

Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bvector.
Import VectorNotations.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Import MonadNotation.
Open Scope monad_scope.
Open Scope type_scope.

Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Lib.AcornUnsignedAdders.

(* Test vector based adder *)

(******************************************************************************)
(* Some handy test vectors                                                   *)
(******************************************************************************)

Definition bv4_0  := N2Bv_sized 4  0.
Definition bv4_1  := N2Bv_sized 4  1.
Definition bv4_3  := N2Bv_sized 4  3.
Definition bv4_15 := N2Bv_sized 4 15.

Definition bv5_0  := N2Bv_sized 5  0.
Definition bv5_4  := N2Bv_sized 5  4.
Definition bv5_30 := N2Bv_sized 5 30.

(* Check 0 + 0 = 0 *)
Example addV0_0 : combinational (addV bv4_0 bv4_0) = bv5_0.
Proof. reflexivity. Qed.

(* Check 15 + 15 = 30 *)
Example addV15_15 : combinational (addV bv4_15 bv4_15) = bv5_30.
Proof. reflexivity. Qed.

(* Check 1 + 3 = 4 *)
Example addV1_3 : combinational (addV bv4_1 bv4_3) = bv5_4.
Proof. reflexivity. Qed.

(* Tests for list based versions. *)

Definition lv4_0  := to_list bv4_0.
Definition lv4_1  := to_list bv4_1.
Definition lv4_3  := to_list bv4_3.
Definition lv4_15 := to_list bv4_15.

Definition lv5_0  := to_list bv5_0.
Definition lv5_4  := to_list bv5_4.
Definition lv5_30 := to_list bv5_30.

(* Check 0 + 0 = 0 *)
Example addL0_0 : combinational (addL lv4_0 lv4_0) = lv5_0.
Proof. reflexivity. Qed.

(* Check 15 + 15 = 30 *)
Example addVL15_15 : combinational (addL lv4_15 lv4_15) = lv5_30.
Proof. reflexivity. Qed.

(* Check 1 + 3 = 4 *)
Example addL1_3 : combinational (addL lv4_1 lv4_3) = lv5_4.
Proof. reflexivity. Qed.