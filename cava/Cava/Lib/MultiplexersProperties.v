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
Require Import Cava.Lib.Multiplexers.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.CombinationalProperties.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.

Lemma mux2_correct {t} (i0 i1 : combType t) (sel : combType Bit) :
  mux2 sel (i0, i1) = if sel then i1 else i0.
Proof. destruct sel; reflexivity. Qed.
Hint Rewrite @mux2_correct using solve [eauto] : simpl_ident.

Lemma mux4_correct {t} (i0 i1 i2 i3 : combType t) (sel : combType (Vec Bit 2)) :
  mux4 (i0,i1,i2,i3) sel =
  if Vector.hd (Vector.tl sel)
  then if Vector.hd sel then i3 else i2
  else if Vector.hd sel then i1 else i0.
Proof.
  cbv in sel. constant_bitvec_cases sel; reflexivity.
Qed.
Hint Rewrite @mux4_correct using solve [eauto] : simpl_ident.
