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

Require Import Coq.Lists.List.

Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.List.
Import ListNotations.

Require Import Cava.Core.Signal.
Require Import Cava.Util.Vector.
Require Import Cava.Util.Tactics.
Require Import Cava.Util.IxMonad.

Import IxMonadNotation.
Open Scope ix_monad_scope.

Section WithSignal.
  Context {signal : SignalType -> Type}.

  (* TODO(blaxill):
     - If we move to delayless loop, this will be the deep embedding of monad fix + delay.
     - Delay could possibly be merged into Ret, if Ret is generalized to add state
   *)

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

  Class Cava :=
    { cava : list SignalType -> Type -> Type;
      monad :> IxMonad Monoid_list_app cava;
      xor2  : signal Bit * signal Bit -> cava [] (signal Bit);
      inv : signal Bit -> cava [] (signal Bit);
      loop_init : forall {i s o body_state}
        (resetval : combType s)
        (body : i * signal s -> cava body_state (o * signal s))
        (input : i),
        cava (s :: body_state) o;
      delay_init : forall {s}
        (resetval : combType s)
        (x : signal s),
        cava [s] (signal s);
   }.

  Context {semantics:Cava}.

  Definition delay {s} (x : signal s) := delay_init (defaultCombValue _) x.
  Definition loop {i s o body_state} body input :=
    @loop_init _ i s o body_state (defaultCombValue _) body input.
  Definition fork2 {t} (x : t) : cava [] (t * t) := ret (x,x).

  (* test circuits *)
  Definition test : signal Bit -> cava [Bit] (signal Bit) := loop (xor2 >=> fork2).
  (* Set Printing Notations. *)
  Definition test2 (i : signal Bit) : cava [Bit;Bit] (signal Bit) :=
    loop
      (loop
         (fun '(i,r1,r2) =>
            r1' <- xor2 (i, r1) ;;
            r2' <- xor2 (r1, r2) ;;
            ret (r2',r1',r2))) i.

  (* same as test2, but with initial values undetermined *)
  Definition test2_init (r1_init r2_init : combType Bit)
             (i : signal Bit) : cava [Bit;Bit] (signal Bit) :=
    loop_init r1_init
             (loop_init r2_init
                       (fun '(i,r1,r2) =>
                          r1' <- xor2 (i, r1) ;;
                          r2' <- xor2 (r1', r2) ;;
                          ret (r2',r1',r2'))) i.

  (* test expressions; make sure notation works as intended *)
  Check (test >=> test >=> inv). (* compose sequential and combinational circuits *)
  Check (fun i =>
           x <- loop (xor2 >=> fork2) i ;;
           inv x). (* loop bind *)


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

End WithSignal.

Section Eval.
  (* from now assume cava is combinational (later this would be done with Cava instance) *)
  Let CavaSpine := @CavaSpine combType.

  (* mealy machine interpretation (single-step)

       if reset=true, then the state values are ignored and output is computed
       based on register reset values *)
  Fixpoint step {o ts} (reset : bool) (c : CavaSpine ts o)
    : signal_values ts -> o * signal_values ts :=
    match c with
    | Ret x => fun _ => (x,tt)
    | Bind x f =>
      fun s =>
        let '(s1,s2) := split_values s in
        let '(y,s1') := step reset x s1 in
        let '(z,s2') := step reset (f y) s2 in
        (z, combine_values s1' s2')
    | LoopInit resetval body input =>
      fun s =>
        let s1 := if reset then resetval else fst s in
        let '(out,s1',s2') := step reset (body (input, s1)) (snd s) in
        (out, (s1', s2'))
    | DelayInit resetval x =>
      fun s =>
        let s1 := if reset then resetval else fst s in
        (s1, (x,tt))
    end.

  Fixpoint default_values {ts} : signal_values ts :=
    match ts with
    | [] => tt
    | t :: ts => (defaultCombValue t, default_values)
    end.

  (* circuit simulation with initial state *)
  Definition simulate_init {i ts o} (c : i -> CavaSpine ts o) (input : list i)
             (init : signal_values ts) : list o :=
    fst (fold_left (fun '(acc,s) i =>
                      let '(o,s') := step false (c i) s in
                      (acc ++ [o], s'))
                   input ([], init)).

  (* circuit simulation *)
  Definition simulate {i ts o} (c : i -> CavaSpine ts o) (input : list i) : list o :=
    match input with
    | [] => []
    | i0 :: input =>
      (* initial step is called with reset=true *)
      let '(o,state) := step true (c i0) default_values in
      o :: simulate_init c input state
    end.

  Existing Instance cava_IxMonad.
  Instance CombinationalSemantics : @Cava combType :=
    {| cava := CavaSpine;
       xor2 := fun i => Ret (xorb (fst i) (snd i));
       inv := fun i => Ret (negb i) ;
       loop_init := @LoopInit _;
       delay_init := @DelayInit _;
    |}.

  (* t   0 1 2 3 4 5 6
       in  1 1 1 1 1 1 1
       reg 0 1 0 1 0 1 0
       out 1 0 1 0 1 0 1 *)
  Compute (simulate test (repeat true 10)).
  (*      = [true; false; true; false; true; false; true; false; true; false] *)

  (* starting with r1=0, r2=0:

       t   0 1 2 3 4 5 6
       in  1 1 1 1 1 1 1
       r1  0 1 0 1 0 1 0
       r2  0 1 1 0 0 1 1
       out 1 1 0 0 1 1 0
   *)
  Compute (simulate test2 (repeat true 10)).
  (*      = [true; true; false; false; true; true; false; false; true; true] *)

  (* starting with r1=1, r2=1:
       t   0 1 2 3 4 5 6
       in  1 1 1 1 1 1 1
       r1  1 0 1 0 1 0 1
       r2  1 1 0 0 1 1 0
       out 1 0 0 1 1 0 0
   *)
  Compute (simulate (test2_init true true) (repeat true 10)).
  (*      = [true; false; false; true; true; false; false; true; true; false] *)

End Eval.
