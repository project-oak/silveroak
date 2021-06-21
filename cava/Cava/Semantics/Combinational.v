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
Require Import Coq.NArith.NArith.
Require Import ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Cava.Core.Core.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.Identity.
Require Import Cava.Util.Vector.

Import ListNotations.
Existing Instance combType.

(******************************************************************************)
(* A boolean combinational logic interpretation for the Cava class            *)
(******************************************************************************)

Definition nandb b1 b2 : bool := negb (andb b1 b2).
Definition norb b1 b2 : bool := negb (orb b1 b2).
Definition xnorb b1 b2 : bool := negb (xorb b1 b2).

(******************************************************************************)
(* Instantiate the Cava class for a boolean combinational logic               *)
(* interpretation.                                                            *)
(******************************************************************************)

Instance CombinationalSemantics : Cava combType | 10 :=
  { cava := ident;
    monad := Monad_ident;
    constant := fun x => x;
    constantV := fun _ _ v => v;
    defaultSignal t := defaultCombValue t;
    inv := fun x => ret (negb x);
    and2 :=  fun '(x,y) => ret (andb x y);
    nand2 :=  fun '(x,y) => ret (nandb x y);
    or2 :=  fun '(x,y) => ret (orb x y);
    nor2 :=  fun '(x,y) => ret (norb x y);
    xor2 :=  fun '(x,y) => ret (xorb x y);
    xnor2 :=  fun '(x,y) => ret (xnorb x y);
    buf_gate := ret;
    lut1 := fun f a => ret (f a);
    lut2 := fun f '(a,b) => ret (f a b);
    lut3 := fun f '(a,b,c) => ret (f a b c);
    lut4 := fun f '(a,b,c,d) => ret (f a b c d);
    lut5 := fun f '(a,b,c,d,e) => ret (f a b c d e);
    lut6 := fun f '(a,b,c,d,e,g) => ret (f a b c d e g);
    xorcy := fun '(x,y) => ret (xorb x y);
    muxcy := fun sel x y => ret (if sel then x else y);
    unpackV _ _ v := ret v;
    packV _ _ v := ret v;
    indexAt t sz isz := fun v sel => ret (nth_default (defaultCombSignal _) (N.to_nat (Bv2N sel)) v);
    unsignedAdd m n a := ret (unsignedAddBool a);
    unsignedMult m n a := ret (unsignedMultBool a);
    greaterThanOrEqual m n a := ret (greaterThanOrEqualBool a);
    localSignal _ v := ret v;
    instantiate intf circuit args := circuit args;
    blackBox intf _ := defaultCombValue _
  }.

(* Run circuit for a single step *)
Fixpoint step {i o} (c : Circuit i o)
  : value (circuit_state c) -> value i -> value (circuit_state c) * value o :=
  match c in Circuit i o return value (circuit_state c) -> value i
                                -> value (circuit_state c) * value o with
  | Comb f => fun _ i => (tt, f i)
  | Compose f g =>
    fun cs input =>
      let '(cs1, x) := step f (fst cs) input in
      let '(cs2, y) := step g (snd cs) x in
      (cs1, cs2, y)
  | First f =>
    fun cs input =>
      let '(cs', x) := step f cs (fst input) in
      (cs', (x, snd input))
  | Second f =>
    fun cs input =>
      let '(cs', x) := step f cs (snd input) in
      (cs', (fst input, x))
  | LoopInitCE _ f =>
    fun '(cs,st) '(input, en) =>
      let '(cs', (out, st')) := step f cs (input, st) in
      let new_state := if en then st' else st in
      (cs', new_state, out)
  | DelayInitCE _ =>
    fun st '(input, en) =>
      let new_state := if en then input else st in
      (new_state, st)
  end.

(* Automation to help simplify expressions using the identity monad *)
Create HintDb simpl_ident.
Hint Rewrite @foldLM_ident_fold_left using solve [eauto] : simpl_ident.
Ltac simpl_ident :=
  (* simplify identity monad and most projections from Cava *)
  cbn [fst snd bind ret Monad_ident monad
           constantV packV unpackV constant buf_gate
           inv and2 nand2 or2 nor2 xor2 xnor2
           lut1 lut2 lut3 lut4 lut5 lut6
           xorcy muxcy
           CombinationalSemantics
           ];
  repeat lazymatch goal with
         | |- context [(@Traversable.mapT
                         _ (@Traversable_vector ?n)
                         ?m (@Monad.Applicative_Monad ?m Monad_ident)
                         ?A ?B ?f ?v)] =>
           change (@Traversable.mapT
                     _ (@Traversable_vector n)
                     m (@Monad.Applicative_Monad m Monad_ident)
                     A B f v) with (@Vector.map A B f n v)
         | _ => progress autorewrite with simpl_ident; cbn [fst snd]
         end.
