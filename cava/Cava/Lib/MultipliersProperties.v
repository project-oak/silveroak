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

Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import Cava.Core.Core.
Require Import Cava.Lib.AddersProperties.
Require Import Cava.Lib.CavaPreludeProperties.
Require Import Cava.Lib.CombinatorsProperties.
Require Import Cava.Lib.MultiplexersProperties.
Require Import Cava.Lib.Multipliers.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Vector.
Import VectorNotations.

Lemma squareN_correct n (input : combType (Vec Bit n)) :
  squareN input = N2Bv_sized n (Bv2N input * Bv2N input).
Proof.
  induction n; [ apply nil_eq | ].
  cbn [squareN]. cbv [mcompose]. simpl_ident.
  rewrite IHn. rewrite (eta input).
  autorewrite with vsimpl.
  rewrite !Bv2N_cons.
  rewrite !shiftout_cons, !shiftout_cons0.
  rewrite !N2Bv_sized_add_idemp_r.
  destruct_one_match.
  { apply Bv2N_inj.
    rewrite !N2Bv_sized_mul_idemp_r.
    rewrite <-!N2Bv_sized_double.
    rewrite !N2Bv_sized_add_idemp_l.
    lazymatch goal with
    | |- context [N2Bv_sized ?n (?x + (Bv2N (N2Bv_sized ?n ?y) + ?z))] =>
      replace (x + (Bv2N (N2Bv_sized n y) + z))%N with
          (x + z + Bv2N (N2Bv_sized n y))%N by lia
    end.
    rewrite !N2Bv_sized_add_idemp_r.
    change N.double with (N.mul 2).
    rewrite !N.succ_double_spec.
    repeat (f_equal; try lia). }
  { rewrite <-!N.double_mul.
    rewrite N2Bv_sized_double.
    rewrite N2Bv_sized_mul_idemp_r.
    change N.double with (N.mul 2).
    repeat (f_equal; try lia). }
Qed.
Hint Rewrite @squareN_correct using solve [eauto] : simpl_ident.
