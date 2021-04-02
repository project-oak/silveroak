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

Require Import Cava.Cava.
Require Import Cava.Lib.VecConstEq.

Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.Tactics.

Require Import Cava.Lib.CavaPreludeProperties.
Require Import Cava.Lib.CombinationalProperties.


Lemma vec_const_eq_correct' : forall n k v,
  VecConstEq.vecConstEq n k v = eqb (N2Bv_sized n (N.of_nat k), v).
Proof.
  intros.
  cbv [VecConstEq.vecConstEq eqb].
  simpl_ident.
  rewrite Vector.map2_swap.
  apply f_equal.
  apply Vector.map2_ext.
  intros.
  destruct a; destruct b; trivial.
Qed.
Hint Rewrite @vec_const_eq_correct' using solve [eauto] : simpl_ident.

Lemma vec_const_eq_correct : forall n k v,
  VecConstEq.vecConstEq n k v = combType_eqb (t:=Vec Bit n) (N2Bv_sized n (N.of_nat k)) v.
Proof.
  intros.
  replace (N2Bv_sized n (N.of_nat k)) with (fst ((N2Bv_sized n (N.of_nat k)),v)).
  2:trivial.
  replace v with (snd ((N2Bv_sized n (N.of_nat k)),v)) at 3.
  2:trivial.
  rewrite <- @eqb_correct with (t:=Vec Bit n).
  apply vec_const_eq_correct'.
Qed.
Hint Rewrite @vec_const_eq_correct using solve [eauto] : simpl_ident.
