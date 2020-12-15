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

Require Import Coq.Vectors.Vector.
Require Import ExtLib.Structures.Monads.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.VectorUtils.
Require Import Cava.Monad.MonadFacts.
Require Import Cava.Monad.Identity.
Require Import Cava.Monad.CavaMonad.
Require Import Cava.Lib.BitVectorOps.
Import VectorNotations.

Require Import AesSpec.AddRoundKey.
Require Import AcornAes.AddRoundKey.

Existing Instance CombinationalSemantics.

Section Equivalence.
  Local Notation byte := (Vector.t bool 8).
  Local Notation state := (Vector.t (Vector.t byte 4) 4) (only parsing).
  Local Notation key := (Vector.t (Vector.t byte 4) 4) (only parsing).

  Lemma add_round_key_equiv (k : key) (st : state) :
    let to_words : state -> AddRoundKey.state 32 4 := map flatten in
    let impl := (AcornAes.AddRoundKey.add_round_key k st) in
    let spec := (AesSpec.AddRoundKey.add_round_key
                   32 4 (to_words k) (to_words st)) in
    to_words (unIdent impl) = spec.
  Proof.
    cbv zeta. cbv [AcornAes.AddRoundKey.add_round_key AesSpec.AddRoundKey.add_round_key].
    cbv [xor4x4V xor4xV]. cbv [Bvector.BVxor].
    autorewrite with simpl_ident.
    rewrite map2_map. rewrite map_map2.
    apply map2_ext; intros.
    autorewrite with simpl_ident.
    rewrite map2_flatten with (n:=8) (m:=4).
    f_equal. apply map2_ext; intros.
    autorewrite with simpl_ident.
    reflexivity.
  Qed.
End Equivalence.
