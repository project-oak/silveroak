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
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.List.
Import MonadNotation.

Require Import Cava.Core.Core.
Require Import Cava.Util.BitArithmetic.
Require Import Cava.Util.Identity.
Require Import Cava.Util.Vector.
Require Import Cava.Util.Tuple.

Import ListNotations.
Import FunctorNotation.

Section WithCava.
  Context `{semantics:Cava}.

  Inductive CavaSpine : list SignalType -> Type -> Type :=
  | Ret : forall {t} (x : t), CavaSpine [] t
  | LoopInit :
      forall {i s o body_state}
        (resetval : combType s)
        (body : i * signal s -> CavaSpine body_state (o * signal s))
        (input : i),
        CavaSpine (s :: body_state) o
  | DelayInit : forall {s} (resetval : combType s) (x : signal s), CavaSpine [s] (signal s)
  | Bind :
      forall {t u xs fs} (x : CavaSpine xs t) (f : t -> CavaSpine fs u),
        CavaSpine (xs ++ fs) u
  .

  Instance cava_IxMonad : IxMonad Monoid_list_app CavaSpine :=
  { ret _ x := Ret x;
    bind _ _ _ _ x f := Bind x f;
  }.

  (* simulation helpers *)
  Fixpoint signal_values (ts : list SignalType) : Type :=
    match ts with
    | [] => unit
    | t :: ts' => signal t * signal_values ts'
    end.
  Fixpoint split_values {ts1 ts2 : list SignalType}
    : signal_values (ts1 ++ ts2) -> signal_values ts1 * signal_values ts2 :=
    match ts1 with
    | [] => fun x => (tt, x)
    | t1 :: ts1 =>
      fun x =>
        let rec := split_values (snd x) in
        (fst x, fst rec, snd rec)
    end.
  Fixpoint combine_values {ts1 ts2 : list SignalType}
    : signal_values ts1 -> signal_values ts2 -> signal_values (ts1 ++ ts2) :=
    match ts1 with
    | [] => fun _ y => y
    | t1 :: ts1 =>
      fun x y =>
        let rec := combine_values (snd x) y in
        (fst x, rec)
    end.

End WithCava.

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

Local Fixpoint default_helper (xs: list PortDeclaration): tupledR (port_signal combType <$> xs) :=
  match xs with
  | [] => tt
  | x::xs => (defaultCombValue (port_type x), default_helper xs)
  end.

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
    indexAt t sz isz := fun v sel => ret (nth_default (defaultCombValue _) (N.to_nat (Bv2N sel)) v);
    unsignedAdd m n a := ret (unsignedAddBool a);
    unsignedMult m n a := ret (unsignedMultBool a);
    greaterThanOrEqual m n a := ret (greaterThanOrEqualBool a);
    localSignal _ v := ret v;
    instantiate intf circuit args :=
      uncurry (port_signal combType <$> circuitInputs intf) _ circuit (unbalance' _ args);
    blackBox intf _ :=
      rebalance' (port_signal combType <$> circuitOutputs intf) (default_helper (circuitOutputs intf));
}.

(* Run circuit for a single step *)
Fixpoint step {i o} (c : Circuit i o)
  : circuit_state c -> i -> o * circuit_state c :=
  match c in Circuit i o return circuit_state c -> i
                                -> o * circuit_state c with
  | Comb f => fun _ i => (f i, tt)
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
           port_signal
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
