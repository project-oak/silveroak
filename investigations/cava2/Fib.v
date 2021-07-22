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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Cava.Util.List. (* TODO: From cava 1 *)

Require Import Cava.Types.
Require Import Cava.Expr.
Require Import Cava.Semantics.

Section Var.
  Context {var : tvar}.

  Definition fibonacci {sz: nat}: Circuit (Nat ** Nat) [] Nat := {{
    let/delay r1 :=
      let r2 := delay r1 initially (2^sz-1:denote_type Nat) in
      `AddMod sz` r1 r2
      initially (1:denote_type Nat) in
    r1
  }}.
End Var.

Require Import Coq.Lists.List.
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
  end.

Definition spec_of_fibonacci (sz : nat) (input : list unit) : list nat
  := map (fun n => fibonacci_nat n mod (2 ^ sz)) (seq 0 (List.length input)).

Lemma fork2_step A state input : step (fork2 (A:=A)) state (input, tt) = (tt, (input, input)).
Proof. reflexivity. Qed.

Lemma fibonacci_step sz state input :
  step (fibonacci (sz:=sz)) state input
  = let sum := (fst state + snd state) mod (2 ^ sz) in
    (sum, fst state, sum).
Proof.
  intros; cbn [step fibonacci ].
  repeat (destruct_pair_let; cbn [split_absorbed_denotation combine_absorbed_denotation List.app absorb_any fst snd]).
  reflexivity.
Qed.

Definition fibonacci_invariant {sz}
           (t : nat) (loop_state : nat * nat)
           (output_accumulator : list nat) : Prop :=
  let r1 := fst loop_state in
  let r2 := snd loop_state in
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
  simulate (fibonacci (sz:=sz)) input = spec_of_fibonacci sz input.
Proof.
  cbv [simulate]. rewrite fold_left_accumulate_to_seq with (default:=tt).
  assert (2 ^ sz <> 0) by (apply Nat.pow_nonzero; lia).
  apply fold_left_accumulate_invariant_seq with (I:=fibonacci_invariant (sz:=sz)).
  { cbv [fibonacci_invariant]. ssplit; reflexivity. }
  { cbv [fibonacci_invariant].
    intros; destruct_products; cbn [fst snd] in *; subst; cbn [fst snd].
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
    erewrite <-list_unit_equiv. reflexivity. }
Qed.

