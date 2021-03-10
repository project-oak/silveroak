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
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Lib.CombinatorsProperties.
Require Import Cava.Lib.BitVectorOps.
Require Import Cava.Util.Vector.

Lemma xorV_correct n a b :
  @xorV _ _ n (a,b) = Vector.map2 xorb a b.
Proof.
  intros. cbv [xorV]. cbn [fst snd].
  simpl_ident. apply map2_ext; intros.
  reflexivity.
Qed.
Hint Rewrite @xorV_correct using solve [eauto] : simpl_ident.
