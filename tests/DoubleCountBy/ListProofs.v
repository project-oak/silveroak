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

Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Import ListNotations VectorNotations.
Local Open Scope list_scope.

Require Import ExtLib.Structures.Monads.
Export MonadNotation.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Tactics.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Identity.
Require Import Cava.Acorn.Combinational.
Require Import Cava.Acorn.Combinators.
Require Import Cava.Lib.UnsignedAdders.

Require Import DoubleCountBy.DoubleCountBy.

Existing Instance CombinationalSemantics.

Definition bvadd {n} (a b : Vector.t bool n) : Vector.t bool n :=
  N2Bv_sized n (Bv2N a + Bv2N b).

Definition bvsum {n} (l : list (Vector.t bool n)) : Vector.t bool n :=
  fold_left bvadd l (N2Bv_sized n 0).

Definition bvaddc {n} (a b : Vector.t bool n) : Vector.t bool n * bool :=
  let sum := (Bv2N a + Bv2N b)%N in
  let carry := (Bv2N a <? sum mod (2 ^ N.of_nat n))%N in
  (N2Bv_sized n sum, carry).

Definition bvsumc {n} (l : list (Vector.t bool n)) : Vector.t bool n * bool :=
  fold_left (fun '(acc,_) => bvaddc acc) l (N2Bv_sized n 0, false).

Definition count_by_spec (i : list (Vector.t bool 8)) : list (Vector.t bool 8 * bool) :=
  map (fun t => bvsumc (firstn t i)) (seq 1 (length i)).

Definition double_count_by_spec (i : list (Vector.t bool 8)) : list (Vector.t bool 8 * bool) :=
  map (fun t => bvsumc (firstn t i)) (seq 1 (length i)).

Lemma addN_correct {n} (x y : combType (Vec Bit n)) :
  unIdent (addN (x, y)) = N2Bv_sized n (Bv2N x + Bv2N y).
Admitted.
Hint Rewrite @addN_correct : simpl_ident.

Lemma ltV_correct {n m} x y :
  unIdent (ltV (n:=n) (m:=m) (x, y)) = (Bv2N x <? Bv2N y)%N.
Admitted.
Hint Rewrite @ltV_correct : simpl_ident.

Lemma addC_correct {n} (x y : combType (Vec Bit n)) :
  unIdent (addC (x, y)) = (N2Bv_sized n (Bv2N x + Bv2N y),
                           (Bv2N x <? (Bv2N x + Bv2N y) mod (2 ^ N.of_nat n)))%N.
Proof.
  cbv [addC]. cbv [CombinationalSemantics].
  simpl_ident. rewrite Bv2N_N2Bv_sized_modulo.
  reflexivity.
Qed.

Lemma incrN_correct {n} (x : combType (Vec Bit (S n))) :
  unIdent (incrN x) = N2Bv_sized (S n) (Bv2N x + 1).
Proof.
  cbv [incrN].
  cbv [CombinationalSemantics peel unpeel unsignedAdd unsignedAddBool constant].
  simpl_ident. cbn [Nat.max Nat.add Bv2N N.succ_double].
  (* just proof about shiftout from here *)
Admitted.

Print count_by.
Lemma count_by_correct (input : list (combType (Vec Bit 8))) :
  multistep count_by (tt, (defaultCombValue _, defaultCombValue _)) input
  = count_by_spec input.



Print multistep.
Check addN.
Check (multistep (Comb addN)).

