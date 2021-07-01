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
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Monads.IdentityMonad.
Require Import ExtLib.Data.List.

Require Import Acornish.ListUtils.
Require Import Acornish.Common.

Require Import Cava.Util.List.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope type_scope.

Class Acorn acorn `{Monad acorn} (signal : SignalType -> Type) := {
  inv : signal Bit -> acorn (signal Bit);
  and2 : signal Bit * signal Bit -> acorn (signal Bit);
  addMod : nat -> signal Nat * signal Nat -> acorn (signal Nat);
  natDelay : signal Nat -> acorn (signal Nat);
  loop : (signal Nat * signal Nat -> acorn (signal Nat * signal Nat)) ->
         signal Nat -> acorn (signal Nat);
  constNat : nat -> acorn (signal Nat);
  comparator : signal Nat * signal Nat -> acorn (signal Bit);
  mux2 : signal Bit * (signal Nat * signal Nat) -> acorn (signal Nat);
}.

Inductive CavaDeep: SignalType -> Type :=
| I : forall {a}, nat -> CavaDeep a
| X : forall {a}, CavaDeep a

| Inv : CavaDeep Bit -> CavaDeep Bit
| And2 : CavaDeep Bit * CavaDeep Bit -> CavaDeep Bit
| AddMod : nat -> CavaDeep Nat * CavaDeep Nat -> CavaDeep Nat
| NatDelay : CavaDeep Nat -> CavaDeep Nat
| ConstNat : nat -> CavaDeep Nat
| Comparator : CavaDeep Nat * CavaDeep Nat -> CavaDeep Bit
| Mux2 : CavaDeep Bit * (CavaDeep Nat * CavaDeep Nat) -> CavaDeep Nat
.

Inductive Spine: Type -> Type :=
  | Return : forall {t} (x : t), Spine t
  | Bind : forall {t u} (x : Spine t) (f : t -> Spine u), Spine u
  | Fix : forall {t} (reset: t) (f : t -> Spine t), Spine t
  .

Instance MonadSpine : Monad Spine :=
{ ret x := Return
; bind _ _ := Bind
}.

Instance AcornSimulation : Acorn Spine CavaDeep := {
  inv i := ret (Inv i);
  and2 i := ret (And2 i);
  addMod modBy i := ret (AddMod modBy i);
  natDelay i := ret (NatDelay i);
  loop f i :=
    s' <- Fix X (fun s => x <- f (i,s);; ret (snd x)  ) ;;
    o' <- f (i,s') ;;
    ret (fst o');
  constNat n := ret (ConstNat n);
  comparator i := ret (Comparator i);
  mux2 i := ret (Mux2 i)
}.

Fixpoint flatten' {o} (c: Spine o) : o :=
  match c in Spine o return o with
  | Return x => x
  | Bind x f => flatten' (f (flatten' x))
  | Fix reset f =>
    let v := flatten' (f reset) in
    let v := flatten' (f v) in
    let v := flatten' (f v) in
    v
  end.

Fixpoint state_shape {o} (c: CavaDeep o): list SignalType :=
match c with
| I _ => []
| X => []
| Inv x => state_shape x
| And2 x => state_shape (fst x) ++ state_shape (snd x)
| AddMod _ x => state_shape (fst x) ++ state_shape (snd x)
| NatDelay x => state_shape x ++ [Nat]
| ConstNat _ => []
| Comparator x => state_shape (fst x) ++ state_shape (snd x)
| Mux2 x => state_shape (fst x) ++ state_shape (fst (snd x)) ++ state_shape (snd (snd x))
end.

Definition get t1 t2 : denoteSignal t1 -> denoteSignal t2 :=
  match t1 with
  | Bit =>
    match t2 with
    | Bit => id
    | _ => fun _=> resetVal _
    end
  | Nat =>
    match t2 with
    | Nat => id
    | _ => fun _=> resetVal _
    end
  end.

Definition input_map := nat -> {t&denoteSignal t}.

Fixpoint step {o} (c: CavaDeep o) (input: input_map)
  : denote_list denoteSignal (state_shape c) -> denote_list denoteSignal (state_shape c) * denoteSignal o :=
match c with
| X => fun _ => (tt, resetVal _)
| @I x n => fun _ =>
  let v := input n in
  (tt, (get (projT1 v) x (projT2 v)))
| Inv x => fun s =>
  let (s', o) := step x input s in
  (s', negb o)
| And2 xy => fun s =>
  let (sx,sy) := split_values s in
  let (sx', x) := step (fst xy) input sx in
  let (sy', y) := step (snd xy) input sy in
  (combine_values sx' sy', andb x y)
| AddMod modBy xy => fun s =>
  let (sx,sy) := split_values s in
  let (sx', x) := step (fst xy) input sx in
  let (sy', y) := step (snd xy) input sy in
  (combine_values sx' sy', (x+y) mod modBy)
| NatDelay x => fun s =>
  let (sx, so) := split_values s in
  let (s', o) := step x input sx in
  (combine_values (y:=[_]) s' (o,tt), fst so)
| ConstNat n => fun s =>
  (tt, n)
| Comparator xy => fun s =>
  let (sx,sy) := split_values s in
  let (sx', x) := step (fst xy) input sx in
  let (sy', y) := step (snd xy) input sy in
  (combine_values sx' sy', y <=? x)
| Mux2 ixy => fun s =>
  let (si, sxy) := split_values s in
  let (sx, sy) := split_values sxy in
  let (si', i) := step (fst ixy) input si in
  let (sx', x) := step (fst (snd ixy)) input sx in
  let (sy', y) := step (snd (snd ixy)) input sy in
  (combine_values si' (combine_values sx' sy'), if i then x else y)
end.

(* Run a circuit for many timesteps, starting at the reset value *)
Definition simulate {o} (c : CavaDeep o) (input : list input_map) : list (denoteSignal o) :=
  fold_left_accumulate (fun i s => step c s i) input (resetVals (state_shape c)).

Section WithAcorn.
  Context {acorn} {signal} `{Acorn acorn signal}.

  (* Take a wire and fork it into two branches. *)
  Definition fork2 {t : SignalType}
              (a : signal t) : acorn (signal t * signal t) :=
    ret (a, a).

  (* Take a pair input and apply the circuit r to just the first element. *)
  Definition fsT {t1 t2 t3 : SignalType}
            (f : signal t1 -> acorn (signal t3))
            (ab : signal t1 * signal t2) : acorn (signal t3 * signal t2) :=
    let (a, b) := ab in
    o <- f a ;;
    ret (o, b).

  (* Take a pair input and apply the circuit r to just the second element. *)
  Definition snD {t1 t2 t3 : SignalType}
            (f : signal t2 -> acorn (signal t3))
            (ab : signal t1 * signal t2) : acorn (signal t1 * signal t3) :=
    let (a, b) := ab in
    o <- f b ;;
    ret (a, o).

  (* A circuit which delays the second element of a pair and then performs
     a 256-bit addition of the two values in the pair. *)
  Definition circuit1 : signal Nat * signal Nat -> acorn (signal Nat) :=
    snD natDelay >=> addMod 256.

  Definition counter6 : signal Nat -> acorn (signal Nat) :=
    loop (addMod 6 >=> natDelay >=> fork2).
  (*   loop (addMod 6 >=> fork2). *)

  Definition nestedloop : signal Nat -> acorn (signal Nat) :=
    (* loop (addMod 512 >=> loop (addMod 512 >=> fork2) >=> fork2). *)
    loop (snD natDelay >=> addMod 512 >=> loop (snD natDelay >=> addMod 512 >=> fork2) >=> fork2).

(*   1 _ 1 _ 1 => 1 *)
(*   1 (1) 2 (1) 3 => 3 *)
(*   1 (3) 4 (3) 7 => 7 *)
(*   1 (7) 8 (7) 15 => 15 *)



End WithAcorn.

Compute circuit1.
Compute (flatten' (circuit1 (I 0, I 1))).
Compute (flatten' (counter6 (I 0))).
Compute (flatten' (nestedloop (I 0))).

Compute (simulate (flatten' (circuit1 (I 0, I 1))) (
  [ fun i => existT _ Nat (if Nat.eqb i 0 then 17 else 42)
  ; fun i => existT _ Nat (if Nat.eqb i 0 then 78 else 62)
  ; fun i => existT _ Nat (if Nat.eqb i 0 then 12 else 5)
  ])).

(*
	 = [17; 120; 74]
*)

Compute (simulate (flatten' (counter6 (I 0))) (
  [ fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ])).

Compute (simulate (flatten' (nestedloop (I 0))) (
  [ fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ; fun i => existT _ Nat 1
  ])).



(* = [0; 1; 2; 3; 5; 6; 6] *)
(* = [0; 1; 2; 4; 6; 10; 15] *)
(* = [0; 1; 2; 4; 7; 11; 18] *)
