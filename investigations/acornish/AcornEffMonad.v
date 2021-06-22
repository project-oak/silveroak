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

(* Single monad structure, loop with fused delay *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.List.

Require Import Acornish.EffMonad.
Require Import Acornish.ListUtils.
Require Import Acornish.Common.

Require Import Cava.Util.List.

Import ListNotations.
Import EffMonadNotation.
Local Open Scope eff_monad_scope.
Local Open Scope type_scope.

Class Acorn acorn `{EffMonad (list SignalType) Monoid_list_app acorn} (signal : SignalType -> Type) := {
  inv : signal Bit -> acorn [] (signal Bit);
  and2 : signal Bit * signal Bit -> acorn [] (signal Bit);
  addMod : nat -> signal Nat * signal Nat -> acorn [] (signal Nat);
  natDelay : signal Nat -> acorn [Nat] (signal Nat);
  loop : forall {s}, (signal Nat * signal Nat -> acorn s (signal Nat * signal Nat)) ->
         signal Nat -> acorn (Nat::s) (signal Nat);
  constNat : nat -> acorn [] (signal Nat);
  comparator : signal Nat * signal Nat -> acorn [] (signal Bit);
  mux2 : signal Bit * (signal Nat * signal Nat) -> acorn [] (signal Nat);
}.

Definition step (s: list SignalType) T := denote_list denoteSignal s -> denote_list denoteSignal s*T.

Instance step_eff_monad: EffMonad (x:=list SignalType) (eff:=Monoid_list_app) step :=
{ ret _ x := fun _ => (tt, x)
; bind _ _ _ _ x f := fun s =>
  let '(sx,sf) := split_denotation _ s in
  let '(nsx,x') := x sx in
  let '(nsf,y) := (f x' sf) in
  (combine_denotation _ nsx nsf, y)
}.

Instance AcornSimulation : Acorn step denoteSignal := {
  inv i := fun _ => (tt, negb i);
  and2 '(a, b) := fun _ => (tt, andb a b);
  addMod modBy '(a, b) := fun _ => (tt, (a + b) mod modBy);
  natDelay i := fun '(s, tt) => (i, tt, s);
  loop s f i := fun '(s,s_inner) =>
    let '(ns,(o,s')) := f (i,s) s_inner in
    (s',ns,o);
  constNat n := fun _ => (tt, n);
  comparator '(a,b) := fun _ => (tt, b <=? a);
  mux2 '(sel, (a, b)) := fun _ => (tt, if sel then a else b);
}.

Definition flipper {i o s} (f: i -> s -> s * o) x y := f y x.

(* Run a circuit for many timesteps, starting at the reset value *)
Definition simulate {i o st} (c : i -> step st o) (input : list i) : list o :=
  fold_left_accumulate (flipper c) input (resetVals st).

Section WithAcorn.
  Context {acorn} {signal} `{Acorn acorn signal}.

  (* Take a wire and fork it into two branches. *)
  Definition fork2 {t : SignalType}
              (a : signal t) : acorn [] (signal t * signal t) :=
    ret (a, a).

  (* Take a pair input and apply the circuit r to just the first element. *)
  Definition fsT {t1 t2 t3 : SignalType} {s}
            (f : signal t1 -> acorn s (signal t3))
            (ab : signal t1 * signal t2) : acorn _ (signal t3 * signal t2) :=
    let (a, b) := ab in
    o <- f a ;;
    ret (o, b).

  (* Take a pair input and apply the circuit r to just the second element. *)
  Definition snD {t1 t2 t3 : SignalType} {s}
            (f : signal t2 -> acorn s (signal t3))
            (ab : signal t1 * signal t2) : acorn _ (signal t1 * signal t3) :=
    let (a, b) := ab in
    o <- f b ;;
    ret (a, o).

  (* A circuit which delays the second element of a pair and then performs
     a 256-bit addition of the two values in the pair. *)
  Definition circuit1 : signal Nat * signal Nat -> acorn _ (signal Nat) :=
    snD natDelay >=> addMod 256.

  Definition counter6 : signal Nat -> acorn _ (signal Nat) :=
    (* loop (addMod 6 >=> natDelay >=> fork2). *)
    loop (addMod 6 >=> fork2).

  Definition nestedloop : signal Nat -> acorn _ (signal Nat) :=
    loop (addMod 512 >=> loop (addMod 512 >=> fork2) >=> fork2).
    (* loop (snD natDelay >=> addMod 512 >=> loop (addMod 512 >=> natDelay >=> fork2) >=> fork2). *)

  Definition twoSorter
    (ab: signal Nat * signal Nat) :
    acorn _ (signal Nat*signal Nat) :=
    let a := fst ab in
    let b := snd ab in
    comparison <- comparator (a, b) ;;
    negComparison <- inv comparison ;;
    out0 <- mux2 (comparison, (b, a)) ;;
    out1 <- mux2 (negComparison, (b, a)) ;;
    ret (out0, out1).
  Check twoSorter.

End WithAcorn.

(* We can easily simulate circuits without loops, even if they contain delay elements. *)
Compute (simulate circuit1 (combine [17; 78; 12] [42; 62; 5])).
(*
	 = [17; 120; 74]
*)

Compute (simulate counter6 [1; 1; 1; 1; 1; 1] ).
(*
> = [1; 2; 3; 4; 5; 0]
*)
Compute (simulate counter6 [1; 2; 3; 4; 5; 6] ).
(*
> = [1; 3; 0; 4; 3; 3]
*)

Compute (simulate nestedloop [1; 1; 1; 1; 1; 1] ).
(*
> = [1; 3; 7; 15; 31; 63]
*)

Compute (simulate twoSorter [(1,1); (0,1); (1,0); (1,9); (99,9); (9,0)] ).
(*
> = [(1, 1); (0, 1); (0, 1); (1, 9); (9, 99); (0, 9)]
*)


Definition twoSorterSpec (ab : nat * nat) : nat * nat :=
  let a := fst ab in
  let b := snd ab in
  if (b <=? a) then
    (b, a)
  else
    (a, b).

Compute (twoSorterSpec (1,9)).

Lemma twoSorterCorrect (v : nat * nat) : forall s,
  snd (twoSorter (acorn:=step) v s) = twoSorterSpec v.
Proof.
  intros. cbn in s.
  cbv [twoSorterSpec twoSorter]; cbn.
  destruct (_ <=? _); try reflexivity.
Qed.


