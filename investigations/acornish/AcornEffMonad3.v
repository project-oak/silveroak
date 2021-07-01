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

(* Operational monad style *)

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
         signal Nat -> acorn s (signal Nat);
  constNat : nat -> acorn [] (signal Nat);
  comparator : signal Nat * signal Nat -> acorn [] (signal Bit);
  mux2 : signal Bit * (signal Nat * signal Nat) -> acorn [] (signal Nat);
}.

Inductive Spine: list SignalType -> Type -> Type :=
  | Return : forall {t} (x : t), Spine [] t
  | Delay : forall (reset : nat) (x : nat), Spine [Nat] nat
  | Bind : forall {t u xs fs} (x : Spine xs t) (f : t -> Spine fs u),
        Spine (xs ++ fs) u
  | Loop : forall {fs} (x : nat) (f : nat*nat -> Spine fs (nat * nat)), Spine fs nat
  .

Instance spine_eff_monad: EffMonad (x:=list SignalType) (eff:=Monoid_list_app) Spine :=
{ ret _ x := Return x
; bind _ _ _ _ := Bind
}.

Instance AcornSimulation : Acorn Spine denoteSignal := {
  inv i := Return (negb i);
  and2 '(a, b) := Return (andb a b);
  addMod modBy '(a, b) := Return( (a + b) mod modBy);
  natDelay i := Delay 0 (i);
  loop _ f i := Loop i f;
  constNat n := Return (n);
  comparator '(a,b) := Return (b <=? a);
  mux2 '(sel, (a, b)) := Return (if sel then a else b);
}.

Definition power_fun{I O A S}(f: I*A -> O*A*S): nat -> I*A -> O*A*S :=
  fix rec n :=
    match n with
    | O => f
    | S n' =>
      fun '(i,a) =>
      let '(_, a', _) := rec n' (i,a) in
      f (i,a')
    end.

Fixpoint step_with_gas {o ts} (gas: nat) (c : Spine ts o)
  : denote_list denoteSignal ts -> o * denote_list denoteSignal ts :=
  match c in Spine ts o
  return denote_list denoteSignal ts -> o * denote_list denoteSignal ts
  with
  | Return x => fun _ => (x,tt)
  | Bind x f =>
    fun s =>
      let '(s1,s2) := split_values s in
      let '(y,s1') := step_with_gas gas x s1 in
      let '(z,s2') := step_with_gas gas (f y) s2 in
      (z, combine_values s1' s2')
  | Delay resetval x => fun '(s,tt) => (s, (x, tt))
  | Loop input f => fun s =>
    let f' := fun '(i,a) => step_with_gas gas (f (i,a)) s in
    let '(o,_,s) := power_fun f' gas (input, resetVal Nat) in
    (o,s)
  end.

(* Is this actually useful? *)
Definition circuit_converges {I ts O} (c: I -> Spine ts O) (N:nat):=
  forall i state, exists converged, forall n, n >= N -> step_with_gas n (c i) state = converged.

Definition simulate {i o st} n (c : i -> Spine st o) (input : list i) : list o :=
  fold_left_accumulate (
    fun state input =>
    let '(o,s) := step_with_gas n (c input) state in (s,o)
  ) input (resetVals st).

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
    loop (addMod 6 >=> natDelay >=> fork2).
  Print counter6.
  Definition nestedloop : signal Nat -> acorn _ (signal Nat) :=
    loop (snD natDelay >=> addMod 512 >=> loop (addMod 512 >=> natDelay >=> fork2) >=> fork2).

End WithAcorn.

(* We can easily simulate circuits without loops, even if they contain delay elements. *)
Compute (simulate 1 circuit1 (combine [17; 78; 12] [42; 62; 5])).
(*
	 = [17; 120; 74]
*)

Compute (simulate 1 counter6 [1; 1; 1; 1; 1; 1] ).
(*
> = [0; 1; 2; 3; 4; 5]
*)
Compute (simulate 1 counter6 [1; 2; 3; 4; 5; 6] ).
(*
> = [0; 1; 3; 0; 4; 3]
*)

Compute (simulate 1 nestedloop [1; 1; 1; 1; 1; 1] ).
(*
> = [0; 1; 2; 4; 7; 12]
*)
