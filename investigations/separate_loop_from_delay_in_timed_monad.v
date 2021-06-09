Require Import Coq.Lists.List. Import ListNotations.

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

Definition delay{A}(x: timed (combType A)): timed (combType A) :=
  fun t =>
    match t with
    | 0 => defaultCombValue A
    | S t' => x t'
    end.

Definition incr(x: combType Nat): timed (combType Nat) :=
  ret (x + 1).

Definition decr(x: combType Nat): timed (combType Nat) :=
  ret (x - 1).

Definition add(x y: combType Nat): timed (combType Nat) :=
  ret (x + y).

Definition countUp: timed (combType Nat) := fun t => t.

(* https://github.com/project-oak/silveroak/blob/0adc80b5194a54afff21b7648dea4d3993dc2ea2/cava/Cava/Acorn/SequentialTimed.v
defines loopSeqF, which does a loop and a delay in the same construct.
Can we define a construct that just adds the loop, but no delay?
*)

Module loop_bodies_with_cava_signatures.
  Definition sample_loop_body_without_delay:
    combType Nat * combType Nat -> timed (combType Nat) :=
    fun '(inp, sum) =>
      res <- add inp sum;;
      res' <- incr res;;
      res'' <- decr res';;
      ret res''.

  Definition sample_loop_body_with_delay:
    combType Nat * combType Nat -> timed (combType Nat) :=
    fun '(inp, sum) =>
      res <- add inp sum;;
      res' <- delay (incr res);;
      res'' <- decr res';;
      ret res''.

  Definition loop {A B: SignalType}
             (f: combType A * combType B -> timed (combType B))
             (a: timed (combType A)): timed (combType B).
    refine (fix rec(t: nat) :=
              match t with
              | 0 => defaultCombValue B
              | S t_minus_one => _
              end).
    refine (f (a t, rec t) t).
    Fail Defined. (* Recursive definition of rec is ill-formed. *)
  Abort.

  (* maybe delaying the termination checker until a concrete loop body
     is known will help? *)
  Notation "'loop' f" :=
    (fun (a: timed (combType _)) =>
       (fix rec(t: nat): combType _ :=
          match t with
          | 0 => defaultCombValue _
          | S t_minus_one => f (a t, rec (S t_minus_one)) (S t_minus_one)
          end))
      (at level 10).

  Fail Check (loop sample_loop_body_with_delay).
  (* Nope: Recursive definition of rec is ill-formed. *)
End loop_bodies_with_cava_signatures.

(* let's try alternative signatures for the loop bodies *)
Definition sample_loop_body_without_delay(inp_signal: timed (combType Nat)):
  timed (combType Nat) -> timed (combType Nat) :=
  fun sum_signal =>
    inp <- inp_signal;;
    sum <- sum_signal;;
    res <- add inp sum;;
    res' <- incr res;;
    res'' <- decr res';;
    ret res''.

Definition sample_loop_body_with_delay(inp_signal: timed (combType Nat)):
  timed (combType Nat) -> timed (combType Nat) :=
  fun sum_signal =>
    inp <- inp_signal;;
    sum <- delay sum_signal;;
    res <- add inp sum;;
    res' <- incr res;;
    res'' <- decr res';;
    ret res''.

Definition loop {B: SignalType}
           (f: timed (combType B) -> timed (combType B)): timed (combType B).
  refine (fix rec(t: nat) :=
            match t with
            | 0 => defaultCombValue B
            | S t_minus_one => _
            end).
  refine (f rec t).
  Fail Defined. (* Recursive definition of rec is ill-formed. *)
Abort.

(* maybe delaying the termination checker until a concrete loop body
     is known will help? *)
Notation "'loop' f" :=
  (fix rec(t: nat): combType _ :=
     match t with
     | 0 => defaultCombValue _
     | S t_minus_one => f rec (S t_minus_one)
     end)
  (at level 10).


Definition simulate{A: Type}(x: timed A)(n: nat): list A :=
  List.map x (List.seq 0 n).

Definition sum_countUp: timed (combType Nat) :=
  loop (sample_loop_body_with_delay countUp).
(* termination checker is happy because it unfolds `sample_loop_body_with_delay`
   and `delay` and simplifies the term until it notices that the recursive
   call is made with a structurally smaller nat *)

Fail Definition sum_countUp_without_delay: timed (combType Nat) :=
  loop (sample_loop_body_without_delay countUp).
(* Recursive definition of rec is ill-formed. *)

Compute simulate sum_countUp 10. (* = [0; 1; 3; 6; 10; 15; 21; 28; 36; 45] *)
