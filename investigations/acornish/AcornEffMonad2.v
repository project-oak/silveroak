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

(* Single monad structure, fuelled monad, loop without fused delay *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Data.List.

Require Import Acornish.EffMonad.
Require Import Acornish.ListUtils.

Require Import Cava.Util.List.

Import ListNotations.
Import EffMonadNotation.
Local Open Scope eff_monad_scope.
Local Open Scope type_scope.

Inductive SignalType :=
  | Bit : SignalType
  | Nat : SignalType.

Class Acorn acorn `{EffMonad (list SignalType) Monoid_list_app acorn} (signal : SignalType -> Type) := {
  inv : signal Bit -> acorn [] (signal Bit);
  and2 : signal Bit * signal Bit -> acorn [] (signal Bit);
  addMod : nat -> signal Nat * signal Nat -> acorn [] (signal Nat);
  natDelay : signal Nat -> acorn [Nat] (signal Nat);
  loop : forall {l s}, (signal Nat * signal l -> acorn s (signal Nat * signal l)) ->
         signal Nat -> acorn s (signal Nat);
  constNat : nat -> acorn [] (signal Nat);
  comparator : signal Nat * signal Nat -> acorn [] (signal Bit);
  mux2 : signal Bit * (signal Nat * signal Nat) -> acorn [] (signal Nat);
}.

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

  Definition nestedloop : signal Nat -> acorn _ (signal Nat) :=
    loop (snD natDelay >=> addMod 512 >=> loop (addMod 512 >=> natDelay >=> fork2) >=> fork2).

End WithAcorn.

Definition denoteSignal (t: SignalType) : Type :=
  match t with
  | Bit => bool
  | Nat => nat
  end.

Definition resetVal (t: SignalType) : denoteSignal t :=
  match t with
  | Bit => false
  | Nat => 0
  end.

Fixpoint resetVals (t: list SignalType) : denote_list denoteSignal t :=
  match t with
  | [] => tt
  | x :: xs => (resetVal x, resetVals xs)
  end.

(* Inductive FixResult: Type -> Type := *)
(* | Thunk : forall {a}, a -> FixResult a *)
(* | Diverged : forall {a}, FixResult a. *)

(* Definition thunk_map {a b} (t: FixResult a): (a-> FixResult b) -> FixResult b := *)
(*   match t with *)
(*   | Diverged => fun _ => Diverged *)
(*   | Thunk x => fun f => f x *)
(*   end. *)

(* Definition step (s: list SignalType) T := *)
(*   denote_list denoteSignal s -> nat -> FixResult (denote_list denoteSignal s*T). *)

(* Instance step_eff_monad: EffMonad (x:=list SignalType) (eff:=Monoid_list_app) step := *)
(* { ret _ x := fun _ => (fun _ => Thunk (tt,x)) *)
(* ; bind _ _ _ _ x f := fun s n => *)
(*     let '(sx,sf) := split_denotation _ s in *)
(*     let x_thunk := x sx n in *)
(*     thunk_map x_thunk (fun x' => *)
(*       let '(nsx,x'') := x' in *)
(*       let y_thunk := (f x'' sf) n in *)
(*       thunk_map y_thunk (fun y => *)
(*         let '(nsf,y') := y in *)
(*         Thunk (combine_denotation _ nsx nsf, y') *)
(*     )) *)
(* }. *)

(* #[refine] Instance AcornSimulation : Acorn step denoteSignal := { *)
(*   inv i := fun _ _ => Thunk (tt, negb i); *)
(*   and2 '(a, b) := fun _ _ => Thunk (tt, andb a b); *)
(*   addMod modBy '(a, b) := fun _ _ => Thunk (tt, (a + b) mod modBy); *)
(*   natDelay i := fun '(s, tt) _ => Thunk (i, tt, s); *)
(*   constNat n := fun _ _ => Thunk (tt, n); *)
(*   comparator '(a,b) := fun _ _ => Thunk (tt, b <=? a); *)
(*   mux2 '(sel, (a, b)) := fun _ _ => Thunk (tt, if sel then a else b); *)

(*   loop l s f i :=  (1* Some crazy loop impl *1) *)

(* }. *)

Definition step (s: list SignalType) T :=
  denote_list denoteSignal s -> nat -> (denote_list denoteSignal s*T).

Instance step_eff_monad: EffMonad (x:=list SignalType) (eff:=Monoid_list_app) step :=
{ ret _ x := fun _ _ => (tt,x)
; bind _ _ _ _ x f := fun s n =>
  let '(sx,sf) := split_denotation _ s in
  let '(nsx,x') := x sx n in
  let '(nsf,y) := (f x' sf n) in
  (combine_denotation _ nsx nsf, y)
}.

Instance AcornSimulation : Acorn step denoteSignal := {
  inv i := fun _ _ => (tt, negb i);
  and2 '(a, b) := fun _ _ => (tt, andb a b);
  addMod modBy '(a, b) := fun _ _ => (tt, (a + b) mod modBy);
  natDelay i := fun '(s, tt) _ => (i, tt, s);
  constNat n := fun _ _ => (tt, n);
  comparator '(a,b) := fun _ _ => (tt, b <=? a);
  mux2 '(sel, (a, b)) := fun _ _ => (tt, if sel then a else b);
  loop l s f i sv gn :=
    let (ns,z) := (fix rec n :=
      match n with
      | O => (sv, (i, resetVal _))
      | S n' =>
        let '(_, (_, lv)) := rec n' in
        let y := f (i, lv) sv gn in
        y
      end) gn
    in (ns,fst z)
}.


Definition flipper {i o s} (f: i -> s -> nat -> s * o) n x y := f y x n.

(* Run a circuit for many timesteps, starting at the reset value *)
Definition simulate {i o st} (c : i -> step st o) (input : list i) : list o :=
  fold_left_accumulate (flipper c 10) input (resetVals st).

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
> = [0; 1; 3; 0; 4; 3]
*)

Compute (simulate nestedloop [1; 1; 1; 1; 1; 1] ).
(*
> = [0; 1; 2; 4; 7; 12]
*)
