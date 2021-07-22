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
Require Import Cava.Util.List.

Inductive type :=
| Unit : type
| Nat : type
| Pair : type -> type -> type
.

Fixpoint denote_type (t: type) :=
  match t with
  | Unit => unit
  | Nat => nat
  | Pair x y => (denote_type x * denote_type y)%type
  end.

Fixpoint absorb_any (x y: type) :=
  match x, y with
  | Unit, x => x
  | x, Unit => x
  | _, _ => Pair x y
  end.

Fixpoint absorb_right (x y: type) :=
  match x, y with
  | x, Unit => x
  | _, _ => Pair x y
  end.

Declare Scope circuit_type_scope.
Delimit Scope circuit_type_scope with circuit_type.
Open Scope circuit_type_scope.
Notation "[ ]" := Unit (format "[ ]") : circuit_type_scope.
Notation "[ x ]" := (Pair x Unit) : circuit_type_scope.
Notation "[ x ; y ; .. ; z ]" := (Pair x (Pair y .. (Pair z Unit) ..)) : circuit_type_scope.
Notation "x ** y" := (Pair x y)(at level 60, right associativity) : circuit_type_scope.
Notation "x ++ y" := (absorb_any x y) (at level 60, right associativity): circuit_type_scope.

Definition tvar : Type := type -> Type.
Existing Class tvar.

Section Vars.
  Inductive Circuit {var: tvar}: type -> type -> type -> Type :=
  | Var : forall {x},     var x -> Circuit [] [] x
  | Abs : forall {s x y z}, (var x -> Circuit s y z) -> Circuit s (x ** y) z
  | App : forall {s1 s2 x y z}, Circuit s1 (x ** y) z -> Circuit s2 [] x -> Circuit (s1 ++ s2) y z

  | Let: forall {x y z s1 s2}, Circuit s1 [] x -> (var x -> Circuit s2 y z) -> Circuit (s1++s2) y z
  (* slightly different fomualtion, but equivalent to loop delay *)
  | LetDelay : forall {x y z s1 s2}, denote_type x
    -> (var x -> Circuit s1 [] x)
    -> (var x -> Circuit s2 y z)
    -> Circuit (x ++ s1 ++ s2) y z

  | Delay: forall {x}, denote_type x -> Circuit x [x] x

  | AddMod : nat -> Circuit [] [Nat; Nat] Nat

  | DestructTuple: forall {x y z s}, Circuit [] [] (x**y) -> (var x -> var y -> Circuit s y z) -> Circuit s y z
  | MakeTuple: forall {x y}, Circuit [] [x;y] (x**y)
  .
End Vars.

Definition split_absorbed_denotation {x y}
  : denote_type (x ++ y) -> denote_type x * denote_type y :=
  match x, y with
  | [],_ => fun x => (tt,x)
  | _,[] => fun x => (x, tt)
  | _, _ => fun x => x
  end.

Definition combine_absorbed_denotation {x y}
  : denote_type x -> denote_type y -> denote_type (x ++ y) :=
  match x,y with
  | [], _ => fun _ y => y
  | _, [] => fun x _ => x
  | _, _ => fun x y => (x,y)
  end.

Fixpoint step {i s o} (c : Circuit s i o)
  : denote_type s -> denote_type i -> denote_type s * denote_type o :=
  match c in Circuit s i o return denote_type s -> denote_type i -> denote_type s * denote_type o with
  | Var x => fun _ _ => (tt, x)
  | Abs f => fun s '(i1,i2) =>
    step (f i1) s i2
  | App f x => fun s i =>
    let '(sf, sx) := split_absorbed_denotation s in
    let '(nsx, x) := step x sx tt in
    let '(nsf, o) := step f sf (x, i) in
    (combine_absorbed_denotation nsf nsx, o)
  | Delay _ => fun s '(i,tt) => (i, s)
  | AddMod n => fun _ '(a,(b,_)) => (tt, (a + b) mod (2 ^ n))
  | Let x f => fun s i =>
    let '(sx, sf) := split_absorbed_denotation s in
    let '(nsx, x) := step x sx tt in
    let '(nsf, o) := step (f x) sf i in
    (combine_absorbed_denotation nsx nsf, o)
  | LetDelay _ x f => fun s i =>
    let '(sx, s12) := split_absorbed_denotation s in
    let '(s1, s2) := split_absorbed_denotation s12 in

    let '(ns1, x) := step (x sx) s1 tt in
    let '(ns2, o) := step (f x) s2 i in

    (combine_absorbed_denotation x (combine_absorbed_denotation ns1 ns2), o)

  | DestructTuple tup f => fun s i =>
    let '(x,y) := (snd (step tup tt tt)) in
    let '(ns, o) := step (f x y) s i in
    (ns, o)
  | MakeTuple => fun _ '(x,(y,_)) =>
    (tt, (x, y))
  end.

Fixpoint default {t: type} : denote_type t :=
  match t with
  | Unit => tt
  | Nat => 0
  | Pair x y => (@default x, @default y)
  end.

Fixpoint reset_state {i s o} (c : Circuit (var:=denote_type) s i o) : denote_type s :=
  match c in Circuit s i o return denote_type s with
  | Var _ => tt
  | Abs f => reset_state (f default)
  | App f x => combine_absorbed_denotation (reset_state f) (reset_state x)
  | Let x f => combine_absorbed_denotation (reset_state x) (reset_state (f default))
  | LetDelay initial x f =>
    combine_absorbed_denotation initial
      (combine_absorbed_denotation (reset_state (x default)) (reset_state (f default)))
  | Delay initial => initial
  | AddMod _ => tt
  | MakeTuple => tt
  | DestructTuple tup f => combine_absorbed_denotation (reset_state tup) (reset_state (f default default))
  end.

Definition simulate {s i o} (c : Circuit (var:=denote_type) s i o) (input : list (denote_type i)) : list (denote_type o) :=
  fold_left_accumulate (step c) input (reset_state c).

Declare Scope expr_scope.
Declare Custom Entry expr.
Delimit Scope expr_scope with expr.

Notation "{{ x }}" := (x)%expr  (at level 1, x custom expr at level 99).
Notation "f x" := (App f x) (in custom expr at level 3, left associativity) : expr_scope.
Notation "x" := (Var x) (in custom expr, x ident) : expr_scope.
Notation "[[ x ]]" := (x)(in custom expr at level 2, x constr at level 99) : expr_scope.
Notation "'fun' x .. y => e" := ( (Abs (fun x => .. (Abs (fun y => e)) ..) )%expr
 ) (in custom expr at level 1, x binder, y binder, e custom expr at level 1) : expr_scope.

Notation "'let' x := a 'in' e" := (Let a (fun x => e))
  (in custom expr at level 1, x pattern at level 4, e at level 7, a at level 1) : expr_scope.
Notation "'let/delay' x := a 'initially' v 'in' b" := (LetDelay v (fun x => a) (fun x => b))
  (in custom expr at level 1, x pattern at level 4, v constr at level 99, b at level 7, a at level 1) : expr_scope.
Notation "'delay' x 'initially' v" := (App (Delay v) x)
  (in custom expr at level 1, x at level 4, v constr at level 7) : expr_scope.

(* Custom entry means we either need to add primitives as explicit notation or
 * provide escaping *)
Notation "'addmod' v" := (AddMod v)
  (in custom expr at level 1, v constr at level 7) : expr_scope.

Notation "( x , y )" := (App (App MakeTuple x) y)
  (in custom expr, x at level 4, y at level 4) : expr_scope.

Section Var.
  Context {var : tvar}.

  Definition test {A} : Circuit [] [A] A := {{
    fun a => let b := a in a
  }}.

  Definition fork2 {A} : Circuit [] [A] (A ** A) := {{
    fun a => (a, a)
  }}.

  (* I've used 'initially' to separate initial values that aren't part of the
   * bind/app phoas structure. e.g.*)
  (* delay _ initialy _ *)
  (* (self referenceing binder equivalent to loop) =*)
  (* let/delay _ := _ initialy _ *)
  Definition fibonacci {sz: nat}: Circuit (Nat ** Nat) [] Nat := {{
    let/delay r1 :=
      let r2 := delay r1 initially (2^sz-1:denote_type Nat) in
      addmod sz r1 r2
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

Inductive FCircuit : nat -> type -> type -> Type :=
| FVar : forall {s x}, nat -> FCircuit s [] x
| FAbs : forall {s x y z}, FCircuit (S s) y z -> FCircuit s (x ** y) z
| FApp : forall {s x y z}, FCircuit s (x ** y) z -> FCircuit s [] x -> FCircuit s y z

| FLet: forall {s x y z }, FCircuit s [] x -> FCircuit (S s) y z -> FCircuit s y z
| FLetDelay : forall {s x y z}, denote_type x
  -> FCircuit (S s) [] x
  -> FCircuit (S s) y z
  -> FCircuit s y z

| FDelay: forall {s x}, denote_type x -> FCircuit s [x] x

| FAddMod : forall {s}, nat -> FCircuit s [Nat; Nat] Nat

| FDestructTuple: forall {s x y z}, FCircuit s [] (x**y) -> FCircuit (S (S s)) y z -> FCircuit s y z
| FMakeTuple: forall {s x y}, FCircuit s [x;y] (x**y)
.

Fixpoint to_first_order {i s o} n (c : Circuit (var:=fun _ => nat) s i o)
  : FCircuit n i o :=
  match c in Circuit _ i o return FCircuit n i o with
  | Var x => FVar x
  | Abs f => FAbs (to_first_order (S n) (f n))
  | App f x => FApp (to_first_order n f) (to_first_order n x)
  | Delay v => FDelay v
  | AddMod n => FAddMod n
  | Let x f => FLet (to_first_order n x) (to_first_order (S n) (f n))
  | LetDelay v x f => FLetDelay v (to_first_order (S n) (x n)) (to_first_order (S n) (f n))
  | DestructTuple tup f =>
    FDestructTuple (to_first_order n tup)
    (to_first_order (S (S n)) (f n (S n)))
  | MakeTuple => FMakeTuple
  end.

Close Scope list_scope.

Fixpoint fo_state {n i o} (c: FCircuit n i o) : type :=
  match c with
  | FVar _ => Unit
  | FAbs f => fo_state f
  | FApp f x => (fo_state f ++ fo_state x)
  | FLet x f => (fo_state f ++ fo_state x)
  | @FLetDelay _ X _ _ t x f => X ++ (fo_state f ++ fo_state x)
  | @FDelay _ X _ => X
  | FAddMod _ => Unit
  | FDestructTuple tup f => (fo_state tup ++ fo_state f)
  | FMakeTuple => Unit
  end.

Definition fib_fo {sz} := to_first_order 0 (fibonacci (sz:=sz)).

Definition get_phoas_state {i o s var} (_: Circuit (var:=var) s i o) := s.

Compute (fib_fo (sz:=12)).
Compute fo_state (fib_fo (sz:=12)).

Goal forall sz, get_phoas_state (var:=fun _ => nat) (fibonacci (sz:=sz)) = fo_state (fib_fo (sz:=sz)).
  intros.
  cbn [ fo_state fib_fo to_first_order fibonacci absorb_any].
  reflexivity.
Qed.
