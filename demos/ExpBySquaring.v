(*|
.. raw:: html

   <link rel="stylesheet" href="tutorial.css" type="text/css" />

.. coq:: none
|*)

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

Require Import Cava.Cava.
Require Import Cava.CavaProperties.
Import Circuit.Notations.

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
==================
Advanced Cava Demo
==================

This set of examples goes a bit further than Cava's tutorial_ and showcases some
advanced features. For a more gentle introduction or setup instructions, the
tutorial is the best place to start.

Here's the high-level overview of what we'll cover:

  1. We'll write one circuit template to capture the logical structure of an
     algorithm, and then show how to *instantiate it with different subcircuits
     in order to perform different computations*.
  2. We'll construct a circuit that efficiently multiplies by any fixed "compile
     time" constant by *constructing the circuit dynamically according to the
     constant*.
  3. We'll prove everything correct *in full generality*, meaning the proofs
     apply to any choice of subcircuits/constants/other parameters!

Some pieces of boilerplate code have been omitted for readability of this
page. You can view the source_ on our GitHub repo to see it, or to step through
the code locally.

In this demo, we'll define a circuit that executes a classic arithmetic
algorithm, exponentiation by squaring (wikipedia_). The pseudocode looks like::

  exp(x,e):
    if e = 0:
      return 1
    r = exp (x, e // 2)
    if e is even:
      return r^2
    else:
      return r^2 * x

Essentially, you can compute ``x^e`` quickly by looking at the bitwise
representation of ``e`` and either multiplying by ``x`` or squaring. This saves
operations in comparison to the naive approach, especially for large numbers. To
compute ``x^19``, for instance, you would need only 8 multiplications instead of
the 18 you would need with a naive approach::

  exp(x,19) = exp(x,9) ^ 2 * x
  exp(x,9) = exp(x,4) ^ 2 * x
  exp(x,4) = exp(x,2) ^ 2
  exp(x,2) = exp(x,1) ^ 2
  exp(x,1) = exp(x,0) ^ 2 * x
  exp(x,0) = 1

If you substitute addition and doubling for multiplication and squaring in this
algorithm, and return 0 instead of 1 in the base case, it will compute
multiplication instead of exponentiation ("multiplication by doubling"). In this
case, you would compute ``x*19`` as::

  exp(x,19) = exp(x,9) * 2 + x
  exp(x,9) = exp(x,4) * 2 + x
  exp(x,4) = exp(x,2) * 2
  exp(x,2) = exp(x,1) * 2
  exp(x,1) = exp(x,0) * 2 + x
  exp(x,0) = 1

For our hardware implementation, we'll assume that ``x`` is a fixed constant
known before we build the circuit, and that we get the exponent as a stream of
bits (most significant bit first). As a circuit diagram, it looks like:

.. image:: expbysquaring.png
   :width: 90%
   :alt: Diagram of the exponentiation-by-squaring circuit.

In Cava, this circuit would be defined as follows:
|*)

  Definition exp_by_squaring {A} (identity : combType A)
             (square : Circuit (signal A) (signal A))
             (multiply : Circuit (signal A) (signal A))
    : Circuit (signal Bit) (signal A) :=
    LoopInit identity
             ((* start: exp[i], r *)
               Second (square >==> (* r^2 *)
                              Comb fork2 >==> (* r^2, r^2 *)
                              Second multiply (* r^2, r^2*x *))
                      >==> (* exp[i], (r^2, r^2*x) *)
                      Comb (uncurry mux2 >=> fork2) (* r', r' *)).

(*|
In order to support both multiplication and exponentiation with the same
definition, we haven't specified yet what exactly our "square" and "multiply"
procedures are. In Cava, you can take subcircuits as *arguments* to your circuit
definition, much like in some programming languages you can pass functions as
arguments to other functions. In pseudocode, this template would be analogous
to::

  exp(identity, square, multiply, e):
    if e = 0:
      return identity
    r = exp(identity, square, multiply, e // 2)
    r2 = square(r)
    if e is even:
      return r2
    else:
      return multiply(r2)

Note that ``multiply`` has only one operand here; since we assume ``x`` is a
fixed constant, the ``multiply`` is already specialized to multiply the input by
``x``.

This circuit is so general that it can actually be adapted for even more
purposes than exponentiation and multiplication. By plugging in a no-op for
``square`` and an incrementer for ``multiply``, we can simply count the high
bits of the input stream:
|*)

  (* count the number of high bits in the input stream *)
  Definition count_ones {n}
    : Circuit (signal Bit) (signal (Vec Bit n)) :=
    exp_by_squaring
      (Vec.of_N 0) (Comb ret) (Comb incrN).

(*|
We can simulate the circuit to check that it has the desired behavior:

.. coq:: none
|*)

End WithCava.

(*||*)

Compute map Bv2N (simulate (count_ones (n:=8))
                           [true;true;true;false;false;true]).

(*|
.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
The ``incrN`` subcircuit adds 1 to the input bitvector without growing the size
of the vector. This component is part of Cava's core library; check out the
reference_ to browse the various verified circuit components that are included.
``Vec.of_N`` is also part of this library; it converts a number of Coq's ``N``
(binary natural numbers) type into a constant Cava bit-vector.

Next, let's try to define multiplication-by-doubling. We'll need to have
subcircuits for addition of a constant and for doubling. For addition, we can
use the ``addN`` circuit that's included in Cava's standard library. Doubling,
however, can be treated as a bitwise operation; we can shift left by one. So
let's define a specific ``double`` circuit separately:
|*)

  (* double a bitvector by adding 0 and truncating *)
  Definition double {n}
    : Circuit (signal (Vec Bit n)) (signal (Vec Bit n)) :=
    Comb (Vec.cons zero >=> Vec.shiftout).

(*|
Now, we can write a circuit that, given a constant ``x``, computes ``x`` times
the input stream:
|*)

  (* multiply x by the input stream *)
  Definition stream_multiply {n} (x : N)
    : Circuit (signal Bit) (signal (Vec Bit n)) :=
    (* Circuit that adds x to the input bitvector *)
    let addx := Comb (fun i => addN (i, Vec.of_N x)) in
    exp_by_squaring (Vec.of_N 0) double addx.

(*|
.. coq:: none
|*)

End WithCava.

(*|
Let's simulate it to see if it works. ``[true;false;false;true]`` is an input
stream that represents the number 9, so this simulation computes ``3*9``.
|*)

(* 3 * 9 = 27 *)
Compute map Bv2N (simulate (stream_multiply (n:=8) 3)
                           [true;false;false;true]).

(*|
The test becomes more readable if we write a quick helper function to convert
numbers into streams:
|*)

(* Helper for simulation: convert a number into a list of bits with the most
   signficant bit first *)
Definition to_stream (x : N) : list bool :=
  (* reverse because N2Bv puts the least significant bit first *)
  rev (Vector.to_list (N2Bv x)).

(* 3 * 9 = 27 *)
Compute map Bv2N (simulate (stream_multiply (n:=8) 3)
                           (to_stream 9)).

(* 5 * 6 = 30 *)
Compute map Bv2N (simulate (stream_multiply (n:=8) 5)
                           (to_stream 6)).

(* 5 * 60 = 300 (bit vector size increased to 16) *)
Compute map Bv2N (simulate (stream_multiply (n:=16) 5)
                           (to_stream 60)).

(*|
.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
So far, so good. But how about exponentiation by squaring? Now, we need one
subcircuit to multiply by a constant and one subcircuit to square the
input. Cava's core library already includes ``squareN``, which squares an input
bit-vector and truncates to the input size, so squaring is taken care of.

However, for multiplication, since one of the operands is a constant, it might
be efficient to construct our circuit in a way that takes advantage of that
fact. In Cava, we can actually write circuits that change structure based on
constant arguments. This circuit multiplies its input by the number ``x``, which
is expressed as Coq's strictly-positive bitvector type, ``positive``.
|*)

  (* construct a circuit to multiply the input by a compile-time
     constant (expressed as a strictly positive Coq bitvector) *)
  Fixpoint mul_const_pos {n} (x : positive)
    : Circuit (signal (Vec Bit n)) (signal (Vec Bit n)) :=
    (match x with
     | 1 => Comb ret
     | y~0 =>
       (* x * i = 2 * y * i *)
       (mul_const_pos y) >==> double
     | y~1 =>
       (* x * i = (2 * y + 1) * i = 2 * y * i + i *)
       Comb fork2 >==> (* i, i *)
            First (mul_const_pos y >==> double) >==> (* 2*y*i, i *)
            Comb addN (* 2*y*i + i *)
     end)%positive.

(*|
In case the syntax here is unfamiliar: the ``match`` here separates three cases,
which correspond to the three constructors of ``positive``. In the first case,
``x = 1``, in which case multiplying by ``x`` is just the identity (``Comb ret``
can be read as "a wire"). In the second case, ``x`` is constructed from another
positive ``y`` with a ``0`` appended to the end, so ``x = 2*y``). In the third
case, ``x`` is constructed from another positive ``y``, but this time with a
``1`` appended to the end, so ``x = 2*y + 1``.

We want to handle the case where ``x = 0`` too, so we can define another wrapper
function on top where ``x`` has the type of Coq's *nonnegative* bit-vectors,
``N``. ``N`` has two constructors; either ``x`` is a zero, or ``x`` is a
positive. So to define our circuit in terms of ``N``, we just produce a circuit
that always returns 0 if ``x`` is zero and call ``mul_const_pos`` to construct
the positive case.
|*)

  (* construct a circuit to multiply the input by a compile-time
     constant (expressed as a nonnegative Coq bitvector) *)
  Definition mul_constN {n} (x : N)
    : Circuit (signal (Vec Bit n)) (signal (Vec Bit n)) :=
    match x with
    | 0%N => Comb (fun _ => ret (Vec.of_N 0))
    | Npos p => mul_const_pos p
    end.

(*|
.. coq:: none
|*)

End WithCava.

(*|
We can try out constructing this circuit for different values of ``x`` to see
how it behaves.
|*)

Eval cbv [mul_constN mul_const_pos] in mul_constN 1.
Eval cbv [mul_constN mul_const_pos] in mul_constN 4.
Eval cbv [mul_constN mul_const_pos] in mul_constN 5.
Eval cbv [mul_constN mul_const_pos] in mul_constN 16.
Eval cbv [mul_constN mul_const_pos] in mul_constN 20.
Eval cbv [mul_constN mul_const_pos] in mul_constN 2048.
Eval cbv [mul_constN mul_const_pos] in mul_constN 100000.

(*|
Here are the circuit diagrams for some of the smaller ones:

.. figure:: mul1.png
   :width: 90%
   :alt: Diagram of a circuit that multiplies by 1
   :align: center

Above: circuit diagram for ``mul_constN 1``.

.. figure:: mul4.png
   :width: 90%
   :alt: Diagram of a circuit that multiplies by 4.
   :align: center

Above: circuit diagram for ``mul_constN 4``.

.. figure:: mul5.png
   :width: 90%
   :alt: Diagram of a circuit that multiplies by 5.
   :align: center

Above: circuit diagram for ``mul_constN 5``.

.. figure:: mul20.png
   :width: 90%
   :alt: Diagram of a circuit that multiplies by 20.
   :align: center

Above: circuit diagram for ``mul_constN 20``. Note that this is the same as
composing ``mul_constN 5`` and ``mul_constN 4``.

.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
Now that we can multiply by constants efficiently, we can build a circuit that
implements exponentiation by squaring:
|*)

  (* raise x to the power of the input stream *)
  Definition stream_exponentiate {n} (x : N)
    : Circuit (signal Bit) (signal (Vec Bit n)) :=
    exp_by_squaring (Vec.of_N 1) (Comb squareN) (mul_constN x).

(*|
.. coq:: none
|*)

End WithCava.

(*|
It works!
|*)

(* Compute 3 ^ 5 = 243 *)
Compute map Bv2N
        (simulate (stream_exponentiate (n:=8) 3)
                  (to_stream 5)).

(* Compute 5 ^ 6 = 15625 *)
Compute map Bv2N
        (simulate (stream_exponentiate (n:=16) 5)
                  (to_stream 6)).

(* Compute 3 ^ 123
   = 48519278097689642681155855396759336072749841943521979872827 *)
Compute map Bv2N
        (simulate (stream_exponentiate (n:=200) 3)
                  (to_stream 123)).

(*|
Now that we've defined all our circuits and tested them a little bit to make
sure they work for some inputs, it's time to prove them correct more
rigorously. The really cool thing about defining these circuits in Coq is that
now we can prove that they behave as expected for *all possible inputs*. We can
even prove that they work for all *constant parameters*, such as the bit-vector
size ``n`` for ``stream_exponentiate`` and the constant ``x`` for
``mul_constN``. In a sense, we're not just proving that our one single circuit
is correct; we're proving that the strategy we use to construct it is *always*
correct. This kind of reasoning is an extremely powerful tool.


First, we'll want to prove that ``exp_by_squaring`` is correct. We'll define a
specification for it in Coq's specification language that captures the crux of
the algorithm.
|*)

Definition exp_by_squaring_spec
           {A} (mulx square : A -> A)
           (id : A) (exponent : list bool) : A :=
  fold_left
    (fun r (bit : bool) => if bit then mulx (square r) else square r)
    exponent id.

(*|
This specification takes a stream of input and produces the output value we
expect from the circuit after that stream of input has been processed. But this
doesn't quite match our circuit's behavior; we'll get intermediate values as
well. We can define a helper function to apply our specification to each prefix
of the input:
|*)

Definition map_stream {A B} (f : list A -> B) (input : list A) : list B
  := map (fun n => f (firstn (S n) input)) (seq 0 (length input)).

(*|
And now, the proof! It more or less comes down to applying a loop-invariant
lemma, using the preconditions about ``square`` and ``multiply`` to rewrite
those expressions, and doing some list manipulations. Just like in the tutorial,
it's our suggestion to focus more on the proof *statements* (the part between
``Lemma`` and ``Proof``) than the proof *bodies* (the part between ``Proof`` and
``Qed``). The former is intended for humans to read and reason about; the latter
is an argument to Coq that the statement is true, and if the Coq typechecker
accepts it then the argument must be valid (unless there's a bug in Coq itself).
|*)

Lemma exp_by_squaring_correct {A}
      (mul_spec square_spec : combType A -> combType A)
      (identity : combType A)
      (square multiply : Circuit (combType A) (combType A))
      (square_correct :
         forall st i, step square st i = (st, square_spec i))
      (multiply_correct :
         forall st i, step multiply st i = (st, mul_spec i))
      (input : list bool) :
  simulate (exp_by_squaring identity square multiply) input
  = map_stream (exp_by_squaring_spec mul_spec square_spec identity)
               input.
Proof.
  cbv [exp_by_squaring map_stream].
  autorewrite with push_simulate.

  (* apply loop invariant lemma *)
  eapply fold_left_accumulate_invariant_seq
    with (I:=fun i st out =>
               out = map (fun n => exp_by_squaring_spec
                                  mul_spec square_spec
                                  identity (firstn (S n) input))
                         (seq 0 i)
               /\ snd st = exp_by_squaring_spec
                       mul_spec square_spec identity (firstn i input)).
  { (* invariant holds in reset state *)
    split; reflexivity. }
  { (* invariant holds through one timestep *)
    cbv zeta; intros. logical_simplify; subst.
    destruct_products. cbn [fst snd] in *. subst.
    cbv [mcompose uncurry]. simpl_ident.
    (* simplify step, rewrite with square/multiply correctness lemmas *)
    repeat first [ progress cbn [fst snd step]
                 | rewrite square_correct
                 | rewrite multiply_correct
                 | destruct_pair_let
                 | progress simpl_ident ].
    (* separate the most recent step from previous steps *)
    autorewrite with pull_snoc natsimpl.
    rewrite (firstn_succ_snoc input _ ltac:(eassumption))
      by (cbn [combType] in *; lia).
    cbv [exp_by_squaring_spec].
    autorewrite with push_list_fold.
    split; reflexivity. }
  { (* invariant implies postcondition *)
    intros; logical_simplify; subst. reflexivity. }
Qed.

(*|
From here, we no longer have to reason about the exponentiation-by-squaring
circuit; we can use this lemma to prove all our other circuits are
correct. Instead, we can reason about ``exp_by_squaring_spec``, with no
circuit-related reasoning. For example, to prove the ``count_ones`` circuit
correct, we first prove that our specification (which is based on the Coq
standard library definition ``count_occ``) matches ``exp_by_squaring_spec``.
|*)

(* helper lemma proving that count_occ is a specialization of
   exp_by_squaring_spec *)
Lemma count_occ_is_exp_by_squaring n l start :
  exp_by_squaring_spec
    (A:=combType (Vec Bit n))
    (fun v => N2Bv_sized n (Bv2N v + 1)) (fun v => v)
    (N2Bv_sized n start) l
  = N2Bv_sized n (N.of_nat (count_occ bool_dec l true) + start).
Proof.
  cbv [exp_by_squaring_spec]. revert start.
  induction l as [|bit l]; [ reflexivity | ].
  intros; cbn [count_occ fold_left].
  destruct bit; destruct_one_match; try congruence; [ ].
  rewrite N2Bv_sized_add_idemp_l.
  rewrite IHl. f_equal. lia.
Qed.

(*|
We can use this lemma to prove that, no matter how many timesteps we run or how
big our bit-vector is, the nth output of ``count_ones`` will be the number of
``true`` values that appear in the first n bits of input, truncated to fit the
bit-vector size. Because we're doing all of this with inductive reasoning, it's
not at all computationally intensive to write such a proof.
|*)

Lemma count_ones_correct n (input : list bool) :
  simulate (count_ones (n:=n)) input
  = map_stream
      (fun l => let count := count_occ bool_dec l true in
             N2Bv_sized n (N.of_nat count))
      input.
Proof.
  intros; cbv [count_ones].
  rewrite exp_by_squaring_correct
    with (mul_spec:=fun v => N2Bv_sized n (Bv2N v + 1))
         (square_spec := fun v : combType (Vec Bit n) => v)
    by (cbn [circuit_state step]; intros;
        lazymatch goal with x : unit |- _ => destruct x end;
        simpl_ident; reflexivity).
  apply map_ext; intros. simpl_ident.
  rewrite count_occ_is_exp_by_squaring.
  f_equal; lia.
Qed.

(*|
To prove that ``stream_multiply`` is correct, we'll first have to prove the
single-step behavior of ``double`` (to satisfy the ``square_correct``
precondition of ``exp_by_squaring_correct``). That proof is pretty quick:
|*)

Lemma double_step n st i :
  step double st i = (st, N2Bv_sized n (Bv2N i + Bv2N i)).
Proof.
  cbv [double step mcompose].
  simpl_ident. rewrite shiftout_cons0.
  apply f_equal2; [ destruct st; reflexivity | ].
  f_equal. lia.
Qed.

(*|
It's useful to write the inverse operation of ``to_stream`` so that
we can talk about the numeric value that the input represents:
|*)

Definition from_stream (l : list bool) : N :=
  Bv2N (Vector.of_list (rev l)).

Lemma from_stream_cons bit l :
  from_stream (bit :: l)
  = ((if bit then 2 ^ (N.of_nat (length l)) else 0)
     + from_stream l)%N.
Proof.
  cbv [from_stream]. cbn [rev].
  rewrite of_list_snoc.
  rewrite app_length; cbn [length].
  rewrite resize_default_id.
  rewrite Bv2N_snoc.
  f_equal.
  autorewrite with push_length;
    reflexivity.
Qed.

(*|
Now, just like for ``count_ones``, we prove that ``exp_by_squaring_spec``
corresponds to multiplication when given the right parameters. We do it in two
steps, because for the inductive logic to work out we have to reason about the
behavior of ``exp_by_squaring_spec`` for *any* starting value, not just 0.
|*)

Lemma multiply_is_exp_by_squaring' n x l start :
  exp_by_squaring_spec
    (A:=combType (Vec Bit n))
    (fun v => N2Bv_sized n (Bv2N v + x))
    (fun v => N2Bv_sized n (Bv2N v + Bv2N v))
    start l
  = N2Bv_sized n (Bv2N start * 2 ^ N.of_nat (length l)
                  + x * from_stream l).
Proof.
  cbv [exp_by_squaring_spec].
  revert start; induction l.
  { intros; cbn.
    rewrite N.mul_0_r, N.add_0_r, N.mul_1_r.
    rewrite N2Bv_sized_Bv2N; reflexivity. }
  { intros. cbn [fold_left]. rewrite IHl.
    rewrite from_stream_cons.
    cbn [length]. rewrite Nat2N.inj_succ, N.pow_succ_r'.
    destruct_one_match;
      autorewrite with pull_N2Bv_sized;
      lazymatch goal with
      | |- context [N2Bv_sized n (Bv2N (N2Bv_sized n ?x) * ?y + ?z)] =>
        rewrite <-(N2Bv_sized_add_idemp_l _ _ z);
          autorewrite with pull_N2Bv_sized
      end;
      apply f_equal; lia. }
Qed.

Lemma multiply_is_exp_by_squaring n x l :
  exp_by_squaring_spec
    (A:=combType (Vec Bit n))
    (fun v => N2Bv_sized n (Bv2N v + x))
    (fun v => N2Bv_sized n (Bv2N v + Bv2N v))
    (N2Bv_sized n 0) l
  = N2Bv_sized n (x * from_stream l).
Proof.
  rewrite multiply_is_exp_by_squaring'.
  rewrite Bv2N_N2Bv_sized_modulo, N.mod_0_l
    by (apply N.pow_nonzero; lia).
  f_equal; lia.
Qed.

(*|
With that, we have all we need to prove ``stream_multiply`` is always correct!
|*)

Lemma stream_multiply_correct n x (input : list bool) :
  simulate (stream_multiply (n:=n) x) input
  = map_stream
      (fun i => N2Bv_sized n (x * (from_stream i)))
      input.
Proof.
  intros; cbv [stream_multiply].
  rewrite @exp_by_squaring_correct
    with (A:=Vec Bit n)
         (mul_spec:=fun v => N2Bv_sized n (Bv2N v + x))
         (square_spec := fun v => N2Bv_sized n (Bv2N v + Bv2N v))
    by first [ solve [apply double_step]
             | cbn [circuit_state step]; intros; simpl_ident;
               lazymatch goal with x : unit |- _ => destruct x end;
               rewrite N2Bv_sized_add_idemp_r; reflexivity ].
  apply map_ext; intros. simpl_ident.
  apply multiply_is_exp_by_squaring.
Qed.

(*|
Now, let's move on to ``stream_exponentiate``. We'll need to prove that
``mul_constN`` is correct first, and to prove that we'll need a proof for
``mul_const_pos``. This proof goes by induction on ``x``:
|*)

Lemma mul_const_pos_step n x st i :
  step (mul_const_pos x) st i = (st, N2Bv_sized n (Bv2N i * Npos x)).
Proof.
  revert st i.
  induction x; cbn [mul_const_pos circuit_state];
    intros; destruct_products;
    repeat lazymatch goal with x : unit |- _ => destruct x end.
  { (* x = y~1 *)
    cbn [step]. repeat (destruct_pair_let; cbn [fst snd]).
    simpl_ident. rewrite double_step, IHx. cbn [fst snd].
    f_equal; [ ].
    autorewrite with pull_N2Bv_sized.
    repeat lazymatch goal with
           | |- context
                 [N2Bv_sized n (Bv2N (N2Bv_sized n ?x) + ?y + ?z)] =>
             replace (Bv2N (N2Bv_sized n x) + y + z)%N
               with (y + z + Bv2N (N2Bv_sized n x))%N by lia;
               autorewrite with pull_N2Bv_sized
           end.
    f_equal; lia. }
  { (* x = y~0 *)
    cbn [step]. repeat (destruct_pair_let; cbn [fst snd]).
    simpl_ident. rewrite double_step, IHx. cbn [fst snd].
    f_equal; [ ].
    autorewrite with pull_N2Bv_sized.
    f_equal; lia. }
  { (* x = 1 *)
    cbn [step]. simpl_ident.
    rewrite N.mul_1_r, N2Bv_sized_Bv2N.
    reflexivity. }
Qed.

Lemma mul_constN_step n x st i :
  step (mul_constN x) st i = (st, N2Bv_sized n (Bv2N i * x)).
Proof.
  cbv [mul_constN].
  destruct x; [ | apply mul_const_pos_step ].
  (* remaining case : x = 0 *)
  cbn [step]. destruct st. simpl_ident.
  rewrite N.mul_0_r. reflexivity.
Qed.

(*|
Just like we did for ``stream_multiply``, we prove that exponentiation matches
``exp_by_squaring_spec`` - first for any start value, and then for a start value
of 1.
|*)

Lemma exponentiate_is_exp_by_squaring' n x l start :
  exp_by_squaring_spec
    (A:=combType (Vec Bit n))
    (fun v => N2Bv_sized n (Bv2N v * x))
    (fun v => N2Bv_sized n (Bv2N v * Bv2N v))
    start l
  = N2Bv_sized n (Bv2N start ^ (2 ^ N.of_nat (length l))
                  * x ^ from_stream l).
Proof.
  cbv [exp_by_squaring_spec].
  revert start; induction l.
  { intros; cbn - [N.pow].
    rewrite !N.pow_0_r, N.pow_1_r, N.mul_1_r.
    rewrite N2Bv_sized_Bv2N; reflexivity. }
  { intros. cbn [fold_left]. rewrite IHl.
    rewrite from_stream_cons.
    cbn [length]. rewrite Nat2N.inj_succ, N.pow_succ_r'.
    destruct_one_match;
      rewrite ?N.add_0_l;
      autorewrite with pull_N2Bv_sized;
      rewrite ?N.pow_mul_r, ?N.pow_add_r;
      lazymatch goal with
      | |- context [N2Bv_sized n (Bv2N (N2Bv_sized n ?x) ^ ?y * ?z)] =>
        rewrite <-(N2Bv_sized_mul_idemp_l _ _ z);
          autorewrite with pull_N2Bv_sized
      end;
      rewrite ?N.pow_2_r, ?N.pow_mul_l;
      apply f_equal; lia. }
Qed.

Lemma exponentiation_is_exp_by_squaring n x l :
  exp_by_squaring_spec
    (A:=combType (Vec Bit n))
    (fun v => N2Bv_sized n (Bv2N v * x))
    (fun v => N2Bv_sized n (Bv2N v * Bv2N v))
    (N2Bv_sized n 1) l
  = N2Bv_sized n (x ^ from_stream l).
Proof.
  rewrite exponentiate_is_exp_by_squaring'.
  assert (2 ^ N.of_nat (length l) <> 0)%N
    by (apply N.pow_nonzero; lia).
  rewrite Bv2N_N2Bv_sized_modulo by lia.
  destruct n; [ apply nil_eq | ].
  rewrite N.mod_1_l by (apply N.pow_gt_1; lia).
  rewrite N.pow_1_l.
  f_equal; lia.
Qed.

(*|
And now we can prove ``stream_exponentiate`` is always correct!
|*)

Lemma stream_exponentiate_correct n x (input : list bool) :
  simulate (stream_exponentiate (n:=n) x) input
  = map_stream
      (fun i => N2Bv_sized n (x ^ (from_stream i)))
      input.
Proof.
  intros; cbv [stream_exponentiate].
  rewrite @exp_by_squaring_correct
    with (A:=Vec Bit n)
         (mul_spec:=fun v => N2Bv_sized n (Bv2N v * x))
         (square_spec := fun v => N2Bv_sized n (Bv2N v * Bv2N v))
    by first [ solve [apply mul_constN_step]
             | cbn [circuit_state step]; intros; simpl_ident;
               lazymatch goal with x : unit |- _ => destruct x end;
               reflexivity ].
  apply map_ext; intros. simpl_ident.
  apply exponentiation_is_exp_by_squaring.
Qed.

(*|
Thanks for bearing with us through the end! For questions, comments, and
contributions, contact us on our GitHub repo_.

.. _reference: ../reference
.. _repo: https://github.com/project-oak/silveroak
.. _tutorial: tutorial
.. _source: https://github.com/project-oak/silveroak/blob/main/demos/ExpBySquaring.v
.. _wikipedia: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
|*)
