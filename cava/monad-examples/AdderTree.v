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

(* A codification of the Lava embedded DSL develope for Haskell into
   Coq for the specification, implementaiton and formal verification of
   circuits. Experimental work, very much in flux, as Satnam learns Coq!
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Vector.
From Coq Require Import Bool.Bvector.
From Coq Require Arith.PeanoNat.
Require Import Omega.

Require Import ExtLib.Structures.Monads.

Require Import Cava.Netlist.
Require Import Cava.BitArithmetic.
Require Import Cava.Monad.Cava.
Require Import Cava.Monad.Combinators.
Require Import Cava.Monad.UnsignedAdders.

Local Open Scope vector_scope.
Set Implicit Arguments.

Definition to_n_plus_n {a n} (v : Vector.t a (2*n)) : Vector.t a (n + n).
Proof.
  intros. simpl in v. rewrite <- plus_n_O in v. apply v.
Defined.

Definition halve' {n a} (v : Vector.t a (n+n)) : Vector.t a n * Vector.t a n :=
  splitat n v.

Definition v0 := nat_to_bitvec_sized 8  4.
Definition v1 := nat_to_bitvec_sized 8 17.
Definition v2 := nat_to_bitvec_sized 8  6.
Definition v3 := nat_to_bitvec_sized 8  3.

Definition v0_3 : Vector.t (Bvector 8) (2+2) := [v0; v1; v2; v3].
(* Compute halve' v0_3. *)

Definition halve {n a} (v : Vector.t a (2*n)) : Vector.t a n * Vector.t a n :=
  halve' (to_n_plus_n v).

Fixpoint adderTree {m bit} `{Cava m bit} (n s : nat) (v : Vector.t (Vector.t bit s) (2^(n+1))) : m (Vector.t bit s) :=
  match n, v with
  | O, v2 => unsignedAdd s (hd v2) (hd (tl v2))
  | S n', vR => let '(vL, vH) := halve vR in
                aS <- adderTree n' vL ;;
                bS <- adderTree n' vH ;;
                sum <- unsignedAdd s aS bS ;;
                ret sum
  end.
 
(* An adder tree with 2 inputs each of 8 bits in size. *)

Definition adderTree2_8 {m bit} `{Cava m bit} (v : Vector.t (Vector.t bit 8) 2) : m (Vector.t bit 8)
  := adderTree 0 v.

Definition v2_8 : Vector.t (Bvector 8) 2 := [v0; v1].
Definition v0_plus_v1 : Bvector 8 := combinational (adderTree2_8 v2_8).
Compute v0_plus_v1.

Example v0_plus_v1_ex : bitvec_to_nat v0_plus_v1 = 21.
Proof. reflexivity. Qed.

(* An adder tree with 4 inputs each of 8 bits in size. *)

Definition adderTree4_8 {m bit} `{Cava m bit} (v : Vector.t (Vector.t bit 8) 4) : m (Vector.t bit 8)
  := adderTree 1 v.

Definition adder_tree4_8_top : state CavaState (Vector.t N 8) :=
  setModuleName "adder_tree4_8" ;;
  a <- inputVectorTo0 8 "a" ;;
  b <- inputVectorTo0 8 "b" ;;
  c <- inputVectorTo0 8 "c" ;;
  d <- inputVectorTo0 8 "d" ;;
  sum <- adderTree4_8 [a; b; c; d] ;;
  outputVectorTo0 8 sum "sum".

Definition adder_tree4_8Netlist := makeNetlist adder_tree4_8_top.

Definition v4_8 : Vector.t (Bvector 8) (2^(1+1)) := [v0; v1; v2; v3].

Definition adderTree4_8_sim : ident (Vector.t bool 8) := adderTree4_8 v4_8.

(*
Compute (combinational adderTree4_8_sim).
*)

(* This computation causes Coq to loop.
Compute (combinational adderTree4_8_sim).
*)

