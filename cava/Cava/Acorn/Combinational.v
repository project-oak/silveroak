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
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.IdentityMonad.
Import MonadNotation.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Circuit.

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

Instance CombinationalSemantics : Cava combType :=
  { cava := ident;
    monad := Monad_ident;
    constant := fun x => x;
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
    unpair _ _ v := v;
    mkpair _ _ v1 v2 := (v1, v2);
    peel _ _ v := v;
    unpeel _ _ v := v;
    indexAt t sz isz := fun v sel => nth_default (defaultCombValue _) (N.to_nat (Bv2N sel)) v;
    indexConst t sz := fun v sel => nth_default (defaultCombValue _) sel v;
    slice t sz startAt len v H := sliceVector v startAt len H;
    unsignedAdd m n := unsignedAddBool;
    unsignedMult m n := unsignedMultBool;
    greaterThanOrEqual m n := greaterThanOrEqualBool;
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefault (map port_type (circuitOutputs intf)));
}.


(* Run a circuit for many timesteps *)
Definition multistep {i o} (c : Circuit i o) (resetvals : circuit_state c)
           (dummy : o) (input : list i) : list o :=
  let '(acc, _) := fold_left_accumulate
                     (fun o_st i => unIdent (interp c (snd o_st) i))
                     input (dummy, resetvals) in
  map fst (tl acc).
