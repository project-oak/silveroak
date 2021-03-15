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

Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Require Import Coq.Vectors.Vector.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadLaws.
Require Import Cava.Core.Core.
Require Import Cava.Lib.Adders.
Require Import Cava.Lib.CavaPrelude.
Require Import Cava.Lib.Combinators.
Require Import Cava.Lib.CombinatorsProperties.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.BitArithmeticProperties.
Require Import Cava.Util.Identity.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.Vector.
Import VectorNotations.
Local Open Scope N_scope.

(* A proof that the half-adder is correct. *)
Lemma halfAdder_behaviour :
  forall (a : bool) (b : bool),
    halfAdder (a, b) = (xorb a b, a && b).
Proof.
  auto.
Qed.

(* A proof that the the full-adder is correct. *)
Lemma fullAdder_behaviour : forall (a : bool) (b : bool) (cin : bool),
    fullAdder (cin, (a, b))
    = (xorb cin (xorb a b),
       (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.

Lemma fullAdder_correct inputs :
  let cin := fst inputs in
  let a := fst (snd inputs) in
  let b := snd (snd inputs) in
  let sum := N.b2n a + N.b2n b + N.b2n cin in
  fullAdder inputs = (N.testbit sum 0, N.testbit sum 1).
Proof. destruct inputs as [cin [a b]]; destruct cin, a, b; reflexivity. Qed.

Lemma addC_correct n inputs :
  let x := fst (fst inputs) in
  let y := snd (fst inputs) in
  let sum := Bv2N x + Bv2N y + N.b2n (snd inputs) in
  addC (n:=n) inputs = (N2Bv_sized n sum, N.testbit_nat sum n).
Proof.
  cbv [addC]. repeat destruct_pair_let. simpl_ident.
  destruct inputs as [[x y] cin]. cbn [fst snd].
  revert x y cin; induction n; intros;
    [ apply case0 with (v:=x); apply case0 with (v:=y);
      destruct cin; reflexivity | ].
  rewrite col_step, fullAdder_correct. cbn [fst snd].
  rewrite (Vector.eta x), (Vector.eta y).
  rewrite vcombine_cons. autorewrite with vsimpl.
  rewrite !Bv2N_cons. cbn [fst snd]. rewrite IHn.
  repeat destruct_one_match; destruct cin;
    repeat lazymatch goal with |- context [N.testbit ?n ?i] =>
                               compute_expr (N.testbit n i) end;
    cbn [N.b2n fst snd].
  all:rewrite <-?N2Bv_sized_double, <-?N2Bv_sized_succ_double.
  all:repeat lazymatch goal with
             | |- context [N.double ?x] => rewrite (N.double_spec x)
             | |- context [N.succ_double ?x] => rewrite (N.succ_double_spec x)
             end.
  all:apply f_equal2; [ f_equal; lia | ].
  all:rewrite <-Ndiv2_correct, N.div2_div.
  all:f_equal; [ ].
  all:first [ apply N.div_unique with (r:=0); lia
            | apply N.div_unique with (r:=1); lia ].
Qed.

Lemma addN_correct n inputs :
  let sum := Bv2N (fst inputs) + Bv2N (snd inputs) in
  addN (n:=n) inputs = N2Bv_sized n sum.
Proof.
  cbv [addN zero]. simpl_ident. repeat destruct_pair_let.
  rewrite addC_correct. cbn [fst snd N.b2n].
  rewrite N.add_0_r. reflexivity.
Qed.

(* A quick sanity check of the Xilinx adder with carry in and out *)
Example xilinx_add_17_52:
  xilinxAdderWithCarry
    (N2Bv_sized 8 17, N2Bv_sized 8 52, false) =
  (N2Bv_sized 8 69, false).
Proof. vm_compute. reflexivity. Qed.

(* A quick sanity check of the Xilinx adder with no bit-growth *)
Example xilinx_no_growth_add_17_52:
  xilinxAdder (N2Bv_sized 8 17) (N2Bv_sized 8 52) =
  (N2Bv_sized 8 69).
Proof. reflexivity. Qed.

(* A proof that the the Xilinx full-adder is correct. *)
Lemma xilinxFullAdder_behaviour :
  forall (a : bool) (b : bool) (cin : bool),
    xilinxFullAdder (cin, (a, b))
    = (xorb cin (xorb a b),
       (a && b) || (b && cin) || (a && cin)).
Proof.
  intros.
  unfold fst.
  simpl.
  case a, b, cin.
  all : reflexivity.
Qed.
