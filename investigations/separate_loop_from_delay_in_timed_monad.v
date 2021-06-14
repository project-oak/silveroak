Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

(* based on https://github.com/project-oak/silveroak/blob/0adc80b5194a54afff21b7648dea4d3993dc2ea2/cava/Cava/Acorn/TimedMonad.v *)

Definition timed(A: Type) := nat -> A.

Definition ret{A: Type}(x: A): timed A := fun t => x.
Definition bind{A B: Type}(x : timed A)(f: A -> timed B): timed B :=
  fun t => f (x t) t.

(* Left-to-right composition of Kleisli arrows. (specialized from coq-ext-lib) *)
Definition mcompose{T U V: Type}(f: T -> timed U)(g: U -> timed V): T -> timed V :=
  fun x => bind (f x) g.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity).
Notation "f >=> g" := (mcompose f g) (at level 61, right associativity).

Inductive SignalType := Bit | Nat.

Definition combType(A: SignalType) :=
  match A with
  | Bit => bool
  | Nat => nat
  end.

Definition defaultCombValue(A: SignalType): combType A :=
  match A with
  | Bit => false
  | Nat => 0
  end.

Definition delayWithInit{A}(init: combType A)(x: timed (combType A)): timed (combType A) :=
  fun t =>
    match t with
    | 0 => init
    | S t' => x t'
    end.

Definition delay{A}(x: timed (combType A)): timed (combType A) :=
  delayWithInit (defaultCombValue A) x.

Definition incr(x: combType Nat): timed (combType Nat) :=
  ret (x + 1).

Definition decr(x: combType Nat): timed (combType Nat) :=
  ret (x - 1).

Definition add(x y: combType Nat): timed (combType Nat) :=
  ret (x + y).

(* https://github.com/project-oak/silveroak/blob/0adc80b5194a54afff21b7648dea4d3993dc2ea2/cava/Cava/Acorn/SequentialTimed.v
defines loopSeqF, which does a loop and a delay in the same construct.
Can we define a construct that just adds the loop, but no delay?
*)

Definition sample_loop_body_with_delay(inp_signal: timed (combType Nat)):
  timed (combType Nat) -> timed (combType Nat) :=
  fun sum_signal =>
    inp <- inp_signal;;
    sum <- delay sum_signal;;
    res <- add inp sum;;
    res' <- incr res;;
    res'' <- decr res';;
    ret res''.

Definition power_fun{A: Type}(f: A -> A): nat -> A -> A :=
  fix rec n :=
    match n with
    | O => id
    | S n' => fun a => f (rec n' a)
    end.

(* trick: if we want to know the value at time t, a fuel amount of (S t) is sufficient
   (assuming that the loop body contains at least one delay), and we can completely
   hide the fact that we use fuel inside the definition of loop *)
Definition loop{B: SignalType}(f: timed (combType B) -> timed (combType B)): timed (combType B) :=
  fun t => power_fun f (S t) (fun _ => defaultCombValue B) t.

(* will be used with A, B, C instantiated to `timed Something` *)
Definition compose{A B C}(f: A -> B)(g: B -> C): A -> C := fun a => g (f a).
Infix ">>" := compose (at level 40).
Definition fork2{A B}(f: A -> B): A -> B * B := fun a => let b := f a in (b, b).
(* Take a pair input and apply the f to just the first element. *)
Definition fsT{A1 A2 B}(f: A1 -> A2)(ab: A1 * B): A2 * B := let (a1, b) := ab in (f a1, b).
(* Take a pair input and apply the f to just the second element. *)
Definition snD{A B1 B2}(f: B1 -> B2)(ab: A * B1): A * B2 := let (a, b1) := ab in (a, f b1).

Definition adder: timed (combType Nat) * timed (combType Nat) -> timed (combType Nat) :=
  fun '(x, y) => v1 <- x;; v2 <- y;; add v1 v2.

Eval cbv -[Nat.add] in adder.

Definition const(A: SignalType)(v: combType A): combType A := v.

Definition simulate{A: Type}(x: timed A)(n: nat): list A :=
  List.map x (List.seq 0 n).

Definition incrementer(x: timed (combType Nat)): timed (combType Nat) :=
  v <- x;; ret (v + 1).

(*
Here's a simple count up loop:

      ---    -------
      |i|    |delay|
  +-->|n|--->|with |--+----->
  |   |c|    |init |  |
  |   |r|    |  0  |  |
  |   ---    -------  |
  |                   |
  +-------------------+
*)
Definition countUp: timed (combType Nat) :=
  loop (incrementer >> (delayWithInit (const Nat 0))).

Compute simulate countUp 10. (* = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9] *)

(* We can pass this countUp loop as an input to another loop body: *)
Definition sum_countUp: timed (combType Nat) :=
  loop (sample_loop_body_with_delay countUp).

Compute simulate sum_countUp 10. (* = [0; 1; 3; 6; 10; 15; 21; 28; 36; 45] *)

(*
Here's a circuit with two delays computing Fibonacci numbers:

      -------      -------   ---
      |delay|      |delay|   | |
  +-->|with |--+-->|with |-->|a|
  |   |init |  |   |init |   |d|
  |   |  1  |  |   |  0  |   |d|--+----->
  |   -------  |   -------   |e|  |
  |            |             |r|  |
  |            +------------>| |  |
  |                          ---  |
  |                               |
  +-------------------------------+

*)
Definition fib_body: timed (combType Nat) -> timed (combType Nat) :=
  (fork2 (delayWithInit (const Nat 1)) >> fsT (delayWithInit (const Nat 0))) >> adder.
Definition fib: timed (combType Nat) := loop fib_body.

Compute simulate fib 10. (* = [1; 2; 3; 5; 8; 13; 21; 34; 55; 89] *)

Definition equalUpTo{A}(t: nat)(x y: timed A) := forall u, u < t -> x u = y u.

Lemma equalUpTo_elim{A}(x y: timed A):
  (forall t, equalUpTo t x y) ->
  forall t, x t = y t.
Proof.
  unfold equalUpTo.
  intros E t.
  apply (E (S t)).
  constructor.
Qed.

Lemma equalUpTo_S{A}(x y: timed A)(t: nat):
  equalUpTo t x y ->
  x t = y t ->
  equalUpTo (S t) x y.
Proof.
  unfold equalUpTo.
  intros E1 E2 u L.
  assert (u = t \/ u < t) as C by lia.
  destruct C as [C | C].
  - subst. exact E2.
  - auto.
Qed.

Definition delaysAtLeast{A B}(f: timed A -> timed B)(d: nat) :=
  forall a1 a2 t, equalUpTo t a1 a2 -> equalUpTo (t + d) (f a1) (f a2).

Lemma power_fun_extra_fuel_has_no_effect{A}(f: timed (combType A) -> timed (combType A))(d: nat):
  delaysAtLeast f (S d) ->
  forall extra t u,
  u < t ->
  power_fun f (t + extra) (fun _ => defaultCombValue A) u =
  power_fun f  t          (fun _ => defaultCombValue A) u.
Proof.
  induction t; intros.
  - exfalso. lia.
  - simpl.
    unfold delaysAtLeast, equalUpTo in H.
    eapply H with (t := u). 2: lia.
    intros. eapply IHt. lia.
Qed.

Lemma loop_fix_aux{A}(f: timed (combType A) -> timed (combType A))(d: nat):
  delaysAtLeast f (S d) ->
  forall t, equalUpTo t (loop f) (f (loop f)).
Proof.
  unfold delaysAtLeast. intros D.
  induction t.
  - unfold equalUpTo.
    intros ? C. inversion C.
  - eapply equalUpTo_S. 1: exact IHt.
    unfold loop at 1. simpl.
    unfold loop.
    unfold equalUpTo in D.
    eapply D with (t := t). 2: lia.
    intros.
    replace t with (S u + (t - S u)) at 1 by lia.
    rewrite (power_fun_extra_fuel_has_no_effect f d D) by lia.
    reflexivity.
Qed.

Lemma loop_fix_without_funext{A}(f: timed (combType A) -> timed (combType A))(d: nat):
  0 < d ->
  delaysAtLeast f d ->
  forall t, loop f t = f (loop f) t.
Proof.
  intros G D t.
  eapply equalUpTo_elim.
  destruct d. 1: inversion G.
  eapply loop_fix_aux. exact D.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma equalUpTo_eq{A}(x y: timed A):
  (forall t, equalUpTo t x y) ->
  x = y.
Proof.
  intro E.
  extensionality t.
  apply equalUpTo_elim.
  exact E.
Qed.

(* If the loop body has a strictly positive delay, `loop` behaves like a fixpoint combinator: *)
Theorem loop_fix{A}(f: timed (combType A) -> timed (combType A))(d: nat):
  0 < d ->
  delaysAtLeast f d ->
  loop f = f (loop f).
Proof.
  intros G D. extensionality t. eapply loop_fix_without_funext; eassumption.
Qed.

Fixpoint fib_spec(n: nat): nat :=
  match n with
  | 0 => 1
  | S n' => match n' with
            | 0 => 2
            | S n'' => fib_spec n'' + fib_spec n'
            end
  end.

Goal simulate fib_spec 10 = simulate fib 10. compute. reflexivity. Qed.

Lemma weaken_equalUpTo{A}(x y: timed A)(t1 t2: nat):
  t1 <= t2 ->
  equalUpTo t2 x y ->
  equalUpTo t1 x y.
Proof.
  unfold equalUpTo. intros. eapply H0. lia.
Qed.

Lemma compose_delaysAtLeast{A B C}(f: timed A -> timed B)(g: timed B -> timed C)(d1 d2: nat):
  delaysAtLeast f d1 ->
  delaysAtLeast g d2 ->
  delaysAtLeast (f >> g) (d1 + d2).
Proof.
  unfold compose, delaysAtLeast. intros. rewrite Nat.add_assoc. eauto.
Qed.

Lemma weaken_delaysAtLeast{A B}(f: timed A -> timed B)(d1 d2: nat):
  delaysAtLeast f d2 ->
  d1 <= d2 ->
  delaysAtLeast f d1.
Proof.
  unfold delaysAtLeast. intros.
  eapply weaken_equalUpTo. 2: eauto. lia.
Qed.

Lemma fib_body_delaysAtLeast: delaysAtLeast fib_body 1.
Proof.
  unfold fib_body.
  eapply weaken_delaysAtLeast. {
    match goal with
    | |- delaysAtLeast (?f >> ?g) _ => eapply (compose_delaysAtLeast f g)
    end.
    (* requires changing signature of fork2 *)
