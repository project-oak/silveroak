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

Require Import Acornish.IxMonad.
Require Import Acornish.ListUtils.
Require Import Acornish.Common.

Require Import Cava.Util.List.

Import ListNotations.
Import IxMonadNotation.
Local Open Scope ix_monad_scope.
Local Open Scope type_scope.

(* Match a SignalType with a reset value to be passed statically around.
   This could also be achieved through other means. *)
Inductive ResetValue : Type :=
  | ResetVal : forall s, denoteSignal s -> ResetValue.

Definition RNat x := ResetVal Nat x.
Definition reset_value_type '(ResetVal s _) := s.
Definition denote_reset '(ResetVal s _) := denoteSignal s.
Definition reset_value_value (v: ResetValue): denote_reset v :=
  match v as r return (denote_reset r) with
  | ResetVal s d => d
  end.

Class Acorn acorn `{IxMonad (list ResetValue) acorn} (signal : SignalType -> Type) := {
  inv : forall {x}, signal Bit -> acorn x x (signal Bit);
  and2 : forall {x}, signal Bit * signal Bit -> acorn x x (signal Bit);
  addMod : forall {x}, nat -> signal Nat * signal Nat -> acorn x x (signal Nat);
  natDelay : forall {x} rst_val, signal Nat -> acorn (RNat rst_val :: x) x (signal Nat);
  loop : forall {i o x y s} (rst_val: denoteSignal s), (i * signal s -> acorn x y (o * signal s)) ->
    i -> acorn (ResetVal s rst_val :: x) y o;
  constNat : forall {x}, nat -> acorn x x (signal Nat);
  comparator : forall {x}, signal Nat * signal Nat -> acorn x x (signal Bit);
  mux2 : forall {x}, signal Bit * (signal Nat * signal Nat) -> acorn x x (signal Nat);
}.

Notation state_term x := (denote_list denote_reset x).
Definition step (is os: list ResetValue) o :=
  state_term is -> state_term os * (state_term os -> state_term is) * o.

Instance step_ix_monad: IxMonad (x:=list ResetValue) step :=
{ ret _ _ x := fun s => (s, id, x)
; bind x1 x2 _ _ _ x f := fun s =>
    let '(p1, p2, p3) := x s in
    let '(f1, f2, f3) := f p3 p1 in
    (f1, fun fx => p2 (f2 fx), f3)
}.

Instance AcornSimulation : Acorn step denoteSignal := {
  inv _ i := fun s => (s, id, negb i);
  and2 _ '(a, b) := fun s => (s, id, andb a b);
  addMod _ modBy '(a, b) := fun s => (s, id, (a + b) mod modBy);
  natDelay _ rst_val i '(s, ss) := (ss, fun s => (i, s), s);
  loop _ _ _ _ _ rst_val f i := fun '(s, s_inner) =>
    let '(s', su, (o, so)) := f (i, s) s_inner in
    (s', fun ns => (so, su ns), o);
  constNat _ n := fun s => (s, id, n);
  comparator _ '(a,b) := fun s => (s, id, b <=? a);
  mux2 _ '(sel, (a, b)) := fun s => (s, id, if sel then a else b);
}.

Definition unpack {i o s} (f: i -> step s [] o) x y :=
  let '(_,ns,o) := f y x in (ns tt, o).

Fixpoint reset (st : list ResetValue): state_term st :=
  match st with
  | [] => tt
  | x :: xs => (reset_value_value x, reset xs)
  end.

(* Run a circuit for many timesteps, starting at the reset value *)
Definition simulate {i o st} (c : i -> step st [] o) (input : list i): list o :=
  fold_left_accumulate (unpack c) input (reset st).

Section WithAcorn.
  Context {acorn} {signal} `{Acorn acorn signal}.

  (* Take a wire and fork it into two branches. *)
  Definition fork2 {x} {t : SignalType}
              (a : signal t) : acorn x x (signal t * signal t) :=
    ret (a, a).

  (* Take a pair input and apply the circuit r to just the first element. *)
  Definition fsT {t1 t2 t3 : SignalType} {x y}
            (f : signal t1 -> acorn x y (signal t3))
            (ab : signal t1 * signal t2) : acorn x y (signal t3 * signal t2) :=
    let (a, b) := ab in
    o <- f a ;;
    ret (o, b).

  (* Take a pair input and apply the circuit r to just the second element. *)
  Definition snD {t1 t2 t3 : SignalType} {x y}
            (f : signal t2 -> acorn x y (signal t3))
            (ab : signal t1 * signal t2) : acorn x y (signal t1 * signal t3) :=
    let (a, b) := ab in
    o <- f b ;;
    ret (a, o).

  (* A circuit which delays the second element of a pair and then performs
     a 256-bit addition of the two values in the pair. *)
  Definition circuit1: signal Nat * signal Nat -> acorn _ [] (signal Nat) :=
    snD (natDelay 0) >=> addMod 256.

  Definition counter6 : signal Nat -> acorn _ [] (signal Nat) :=
    (* loop (addMod 6 >=> natDelay >=> fork2). *)
    loop (0:denoteSignal Nat) (addMod 6 >=> fork2).

  Definition nestedloop : signal Nat -> acorn _ [] (signal Nat) :=
    loop (0:denoteSignal Nat) (addMod 512 >=> loop (0:denoteSignal Nat) (addMod 512 >=> fork2) >=> fork2).
    (* loop (snD natDelay >=> addMod 512 >=> loop (addMod 512 >=> natDelay >=> fork2) >=> fork2). *)

  Definition twoSorter
    (ab: signal Nat * signal Nat) :
    acorn _ [] (signal Nat*signal Nat) :=
    let a := fst ab in
    let b := snd ab in
    comparison <- comparator (a, b) ;;
    negComparison <- inv comparison ;;
    out0 <- mux2 (comparison, (b, a)) ;;
    out1 <- mux2 (negComparison, (b, a)) ;;
    ret (out0, out1).

  Definition fibonacci {sz}: acorn _ [] (signal Nat) :=
    loop (1:denoteSignal Nat) (fun '(_,r1) =>
         r2 <- natDelay (2^sz-1) r1 ;;
         sum <- addMod (2^sz) (r1, r2) ;;
         fork2 sum) tt.
  Print fibonacci.

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

(* Fibonacci proof *)

Close Scope type_scope.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.

Fixpoint fibonacci_nat (n : nat) :=
  match n with
  | 0 => 0
  | S m =>
    let f_m := fibonacci_nat m in
    match m with
    | 0 => 1
    | S p => fibonacci_nat p + f_m
    end
  end%nat.

Definition spec_of_fibonacci (sz : nat) (input : list unit) : list nat
  := map (fun n => fibonacci_nat n mod (2 ^ sz)) (seq 0 (List.length input)).

Lemma fibonacci_step sz state :
  fibonacci (acorn:=step) (sz:=sz) state
  = let sum := (fst state + fst (snd state)) mod (2 ^ sz) in
    (tt, fun _ => (sum, (fst state, tt)), sum).
Proof.
  intros;
    cbv [step fibonacci];
    cbn [fst snd natDelay addMod fork2 AcornSimulation denote_list denoteSignal loop bind].
  repeat (destruct_pair_let;
    cbn [fst snd bind ret step_ix_monad split_denotation combine_denotation fork2]).

  repeat match goal with
  | H: state_term _ |- _ => destruct H
  end.
  cbn; repeat f_equal.

  (* :( *)
  Require Import FunctionalExtensionality.
  apply functional_extensionality.
  destruct x.
  f_equal.
Qed.

(* jade's invariant *)
Definition fibonacci_invariant {sz}
           (t : nat) (loop_state : nat * (nat * unit))
           (output_accumulator : list nat) : Prop :=
  let r1 := fst loop_state in
  let r2 := fst (snd loop_state) in
  (* at timestep t... *)
  (* ...r1 holds fibonacci_nat (t-1), or 1 if t=0 *)
  r1 = match t with
       | 0 => 1
       | S t_minus1 => (fibonacci_nat t_minus1) mod (2 ^ sz)
       end
  (* ... and r2 holds fibonacci_nat (t-2), or 1 if t=1, 2^sz-1 if t=0 *)
  /\ r2 = match t with
         | 0 => 2 ^ sz - 1
         | 1 => 1
         | S (S t_minus2) =>(fibonacci_nat t_minus2) mod (2 ^ sz)
         end
  (* ... and the output accumulator matches the circuit spec for the
     inputs so far *)
  /\ output_accumulator = spec_of_fibonacci sz (repeat tt t).

(* Helper lemma for fibonacci_correct *)
Lemma fibonacci_nat_step n :
  fibonacci_nat (S (S n)) = fibonacci_nat (S n) + fibonacci_nat n.
Proof. cbn [fibonacci_nat]. lia. Qed.

Lemma fibonacci_correct sz input :
  simulate (fun _ : unit => fibonacci (sz:=sz)) input = spec_of_fibonacci sz input.
Proof.
  destruct input; try reflexivity.
  cbv [simulate simulate].
  rewrite fold_left_accumulate_to_seq with (default:=tt).
  assert (2 ^ sz <> 0) by (apply Nat.pow_nonzero; lia).
  cbv [unpack].
  cbn [monoid_plus Monoid_list_app app ].
  eapply fold_left_accumulate_invariant_seq with (I:=fibonacci_invariant ).
  { cbv [fibonacci_invariant]. repeat split. }
  { cbv [fibonacci_invariant].
    intros. destruct_products. cbn [fst snd] in *; subst; cbn [fst snd].
    rewrite fibonacci_step. cbn [fst snd].
    repeat destruct_one_match.
    { (* t = 0 case *)
      cbn. rewrite Nat.sub_1_r, Nat.succ_pred by lia.
      rewrite Nat.mod_same, Nat.mod_0_l by lia.
      ssplit; reflexivity. }
    { (* t = 1 case *)
      cbn. rewrite Nat.mod_0_l by lia.
      ssplit; reflexivity. }
    { (* t > 1 case *)
      rewrite Nat.add_mod_idemp_r, Nat.add_mod_idemp_l by lia.
      ssplit.
      { cbn [fibonacci_nat]. f_equal; lia. }
      { reflexivity. }
      { cbv [spec_of_fibonacci].
        autorewrite with push_length.
        rewrite seq_S with (len:=S (S _)).
        autorewrite with natsimpl. rewrite map_app.
        cbn [map]. rewrite fibonacci_nat_step.
        reflexivity. } } }
  { cbv [fibonacci_invariant]. intros.
    logical_simplify; subst.
    autorewrite with push_length.
    cbn [repeat].
    erewrite <-list_unit_equiv. reflexivity. }
Qed.

