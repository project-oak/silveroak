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

(* Bit-vector arithmetic operations for Cava. *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bvector.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Vector.
Require Coq.Strings.HexString.
Import ListNotations.
Local Open Scope list_scope.

(* List and vector functions for conversion between nats and bit-vectors *)

Module N.
  (* Converts list of bits to a binary natural number, interpreting list as
     little-endian *)
  Definition of_list_bits (bits : list bool) : N :=
    Bv2N (Vector.of_list bits).

  (* Converts an N to a (little-endian) list of bits *)
  Definition to_list_bits (n : N) : list bool :=
    Vector.to_list (N2Bv n).

  (* Converts an N to a (little-endian) list of bits of the specified length *)
  Definition to_list_bits_sized (size : nat) (n : N) : list bool :=
    Vector.to_list (N2Bv_sized size n).
End N.

Example b2n_empty : N.of_list_bits [] = 0%N.
Proof. reflexivity. Qed.

Example b2n_0 : N.of_list_bits [false] = 0%N.
Proof. reflexivity. Qed.

Example b2n_1 : N.of_list_bits [true] = 1%N.
Proof. reflexivity. Qed.

Example b2n_10 : N.of_list_bits [false; true] = 2%N.
Proof. reflexivity. Qed.

Example b2n_01 : N.of_list_bits [true; false] = 1%N.
Proof. reflexivity. Qed.

Example b2n_11 : N.of_list_bits [true; true] = 3%N.
Proof. reflexivity. Qed.

Example n2b_0_1 : N.to_list_bits 0 = [].
Proof. reflexivity. Qed.

Example n2b_1_1 : N.to_list_bits 1 = [true].
Proof. reflexivity. Qed.

Example n2b_2_2 : N.to_list_bits 2 = [false; true].
Proof. reflexivity. Qed.

Example n2b_2_3 : N.to_list_bits 3 = [true; true].
Proof. reflexivity. Qed.

(******************************************************************************)
(* Functions useful for Vector operations                                     *)
(******************************************************************************)

Definition bitvec_to_nat {n : nat} (bits : Bvector n) : nat :=
  N.to_nat (Bv2N n bits).

Definition bv3_0 : Bvector 3 := [false; false; false]%vector.
Example bv3_0_ex : bitvec_to_nat bv3_0 = 0.
Proof. reflexivity. Qed.

Definition bv1 : Bvector 1 := [true]%vector.
Example bv1_ex : bitvec_to_nat bv1 = 1.
Proof. reflexivity. Qed.

Definition bv3_1 : Bvector 3 := [true; false; false]%vector.
Example bv3_1_ex : bitvec_to_nat bv3_1 = 1.
Proof. reflexivity. Qed.

Definition bv3_2 : Bvector 3 := [false; true; false]%vector.
Example bv3_2_ex : bitvec_to_nat bv3_2 = 2.
Proof. reflexivity. Qed.

Definition nat_to_bitvec (v : nat) : Bvector (N.size_nat (N.of_nat v)) :=
  N2Bv (N.of_nat v).

Definition nat_to_bitvec_sized (n : nat) (v : nat) : Bvector n :=
  N2Bv_sized n (N.of_nat v).

Example bv3_0_cancellev : nat_to_bitvec_sized 3 0 = bv3_0.
Proof. reflexivity. Qed.

Example bv3_1_cancellev : nat_to_bitvec_sized 3 1 = bv3_1.
Proof. reflexivity. Qed.

Example bv3_2_cancellev : nat_to_bitvec_sized 3 2 = bv3_2.
Proof. reflexivity. Qed.

(******************************************************************************)
(* Functions useful for examples and tests                                    *)
(******************************************************************************)

Definition nat2bool (n : nat) : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

Definition n2bool (n : N) : bool :=
  match n with
  | 0%N => false
  | _   => true
  end.

Definition fromVec := List.map Nat.b2n.
Definition toVec := List.map nat2bool.

Definition Bv2Hex {n} (x: Vector.t bool n) := HexString.of_N (Bv2N x).
Definition Hex2Bv {n} (s : String.string) := N2Bv_sized n (HexString.to_N s).

Definition byte_reverse {n} (x: Vector.t bool (n*8)) := flatten (reverse (reshape (m:=8) x)).

Definition bitvec_to_byte (v : Vector.t bool 8) : Byte.byte :=
  let '(b0,v) := Vector.uncons v in
  let '(b1,v) := Vector.uncons v in
  let '(b2,v) := Vector.uncons v in
  let '(b3,v) := Vector.uncons v in
  let '(b4,v) := Vector.uncons v in
  let '(b5,v) := Vector.uncons v in
  let '(b6,v) := Vector.uncons v in
  let '(b7,v) := Vector.uncons v in
  Byte.of_bits (b0,(b1,(b2,(b3,(b4,(b5,(b6,b7))))))).

Definition byte_to_bitvec (b : Byte.byte) : Vector.t bool 8 :=
  Ndigits.N2Bv_sized 8 (Byte.to_N b).
Definition bitvec_to_bytevec n (v : Vector.t bool (n * 8)) : Vector.t Byte.byte n :=
  Vector.map bitvec_to_byte (reshape v).
Definition bytevec_to_bitvec n (v : Vector.t Byte.byte n) : Vector.t bool (n * 8) :=
  flatten (Vector.map byte_to_bitvec v).

Definition bytevec_to_wordvec
           bytes_per_word n (v : Vector.t Byte.byte (n * bytes_per_word))
  : Vector.t (Vector.t Byte.byte bytes_per_word) n := reshape v.

Definition bitvec_to_wordvec
           bits_per_word n (v : Vector.t bool (n * bits_per_word))
  : Vector.t (Vector.t bool bits_per_word) n := reshape v.

Definition wordvec_to_bytevec
           bytes_per_word {n} (v : Vector.t (Vector.t Byte.byte bytes_per_word) n)
  : Vector.t Byte.byte (n * bytes_per_word) := flatten v.
Definition wordvec_to_bitvec
           bits_per_word {n} (v : Vector.t (Vector.t bool bits_per_word) n)
  : Vector.t bool (n * bits_per_word) := flatten v.

(* Convert the least significant 8 bits of a number to a byte *)
Definition N_to_byte (x : N) : byte :=
  match Byte.of_N (x mod 2^8) with
  | Some b => b
  | None => x00
  end.

Module BigEndianBytes.
  (* evaluate a big-endian list of bytes *)
  Definition concat_bytes (bs : list byte) : N :=
    List.fold_left (fun acc b => N.lor (N.shiftl acc 8) (Byte.to_N b)) bs 0%N.

  (* convert the least significant (n*8) bits of a number to big-endian bytes *)
  Definition N_to_bytes n (x : N) : list byte :=
    List.map (fun i => N_to_byte (N.shiftr x (N.of_nat (n-1-i)*8)))
             (seq 0 n).

  (* convert a big-endian list of bytes to a list of n-byte words (length of list
   must be a multiple of n) *)
  Definition bytes_to_Ns n (x : list byte) : list N :=
    List.map (fun i => concat_bytes (firstn n (skipn (n*i) x))) (seq 0 (length x / n)).
End BigEndianBytes.

Definition byte_xor (x y : byte) : byte := N_to_byte (N.lxor (Byte.to_N x) (Byte.to_N y)).

(******************************************************************************)
(* Arithmetic operations                                                      *)
(******************************************************************************)

Definition unsignedAddBool {m n : nat}
                           (av_bv : Bvector m *  Bvector n)
: Bvector (1 + max m n) :=
  let (av, bv) := av_bv in
  let a := Bv2N av in
  let b := Bv2N bv in
  let sumSize := 1 + max m n in
  let sum := (a + b)%N in
  N2Bv_sized sumSize sum.

Definition unsignedMultBool {m n : nat}
           (av_bv : Bvector m *  Bvector n)
  : Bvector (m + n) :=
  let (av, bv) := av_bv in
  let a := Bv2N av in
  let b := Bv2N bv in
  let product := (a * b)%N in
  N2Bv_sized (m + n) product.

Definition greaterThanOrEqualBool {m n : nat}
           (av_bv : Bvector m *  Bvector n) : bool :=
  let (av, bv) := av_bv in
  (Bv2N bv <=? Bv2N av)%N.
