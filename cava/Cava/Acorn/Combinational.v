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
Import ListNotations MonadNotation.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Acorn.CavaClass.
Require Import Cava.Acorn.Circuit.
Require Import Cava.Acorn.Identity.

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
    unpackV _ _ v := ret v;
    packV _ _ v := ret v;
    indexAt t sz isz := fun v sel => ret (nth_default (defaultCombValue _) (N.to_nat (Bv2N sel)) v);
    indexConst t sz := fun v sel => ret (nth_default (defaultCombValue _) sel v);
    slice t sz startAt len v H := ret (sliceVector v startAt len H);
    unsignedAdd m n a := ret (unsignedAddBool a);
    unsignedMult m n a := ret (unsignedMultBool a);
    greaterThanOrEqual m n a := ret (greaterThanOrEqualBool a);
    localSignal _ v := ret v;
    instantiate _ circuit := circuit;
    blackBox intf _ := ret (tupleInterfaceDefault (map port_type (circuitOutputs intf)));
}.

(* Run circuit for a single step *)
Fixpoint step {i o} (c : Circuit i o)
  : circuit_state c -> i -> o * circuit_state c :=
  match c in Circuit i o return circuit_state c -> i
                                -> o * circuit_state c with
  | Comb f => fun _ i => (unIdent (f i), tt)
  | Compose f g =>
    fun cs input =>
      let '(x, cs1) := step f (fst cs) input in
      let '(y, cs2) := step g (snd cs) x in
      (y, (cs1, cs2))
  | First f =>
    fun cs input =>
      let '(x, cs') := step f cs (fst input) in
      (x, snd input, cs')
  | Second f =>
    fun cs input =>
      let '(x, cs') := step f cs (snd input) in
      (fst input, x, cs')
  | LoopInitCE _ f =>
    fun '(cs,st) '(input, en) =>
      let '(out, st', cs') := step f cs (input, st) in
      let new_state := if en then st' else st in
      (out, (cs',new_state))
  | DelayInitCE _ =>
    fun st '(input, en) =>
      let new_state := if en then input else st in
      (st, new_state)
  end.

(* Automation to help simplify expressions using the identity monad *)
Create HintDb simpl_ident discriminated.
Hint Rewrite @mapT_vector_ident @mapT_vident @mapT_lident using solve [eauto] : simpl_ident.
Ltac simpl_ident :=
  repeat
    first [ progress autorewrite with simpl_ident
          | progress cbn [fst snd bind ret Monad_ident monad
                              packV unpackV constant
                              CombinationalSemantics ] ].
