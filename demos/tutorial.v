(*|
.. raw:: html

   <link rel="stylesheet" href="tutorial.css" type="text/css" />

.. coq:: none
|*)

(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
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

(*|
========
Tutorial
========

Welcome! This is a quick primer for designing circuits with the Cava DSL. This
tutorial will not explain Coq syntax in depth, but will use the same few
patterns throughout; you shouldn't need to be a Coq expert to follow
along. We'll walk through a few small examples end-to-end, showing you how to
define, simulate, and generate netlists for circuits in Cava.

This page (thanks to the Alectryon_ system) allows you to see the Coq output for
each line that has output. Try hovering over the following line (if on mobile,
tap the line):
|*)

Compute (1 + 2).

(*|
See the banner at the top of the page for instructions on how to navigate the proofs.

.. contents:: Table of Contents
   :depth: 2

Setup
=====

If you are viewing this tutorial on the web and just trying to get a general
idea of how Cava works, skip to the next section. If you are trying to write
your own circuits or step through this tutorial locally, here are the
quick-start instructions for installing Cava::

  $ git clone https://github.com/project-oak/silveroak.git
  $ cd silveroak
  $ make update-third_party
  $ make -j4 cava-coq

You can now make the Cava libraries visible to your project by adding the
following lines to your project's ``_CoqProject`` file::

  -R path/to/silveroak/cava/Cava Cava
  -R path/to/silveroak/third_party/coq-ext-lib/theories ExtLib
  -R path/to/silveroak/third_party/bedrock2/deps/coqutil/src/coqutil coqutil

If you don't have an existing project, you can set up a minimal one as follows:

1. Create a new directory
2. Create a file called ``_CoqProject`` in the new directory containing the
   three lines above, with ``path/to/silveroak`` replaced with the path to
   your clone of ``silveroak``
3. Create a new file with a ``.v`` extension and open it with your favorite
   Coq IDE option (``coqide``, Emacs's Proof General, Vim's ``coqtail``, or VS
   Code, among others). The ``_CoqProject`` file should be detected
   automatically; try writing the imports below into the ``.v`` file, and step
   through them to check that everything's working.

The following lines import everything you need to *define* and *simulate* circuits,
as well as some convenience notations:
|*)

Require Import Cava.Cava.
Import Circuit.Notations.

(*|
If you also want to do *proofs* about circuits, you'll need this import also:
|*)

Require Import Cava.CavaProperties.

(*|
Example 1 : Inverter
====================

To start, let's define a 1-bit inverter.
|*)

Definition inverter
           {signal : SignalType -> Type}
           {semantics : Cava signal}
  : Circuit (signal Bit) (signal Bit) :=
  Comb inv.

(*|
A few things to notice here:

* ``SignalType`` is Cava's type system. The inverter is parameterized over
  ``signal``, which converts ``SignalType``\ s to Coq types. ``Bit`` is one
  example of a ``SignalType``; we'll see more examples later on.
* ``Comb`` is short for "combinational"; our inverter has no loops, registers,
  or timing requirements, so it is a purely combinational circuit.
* The inverter is also paramterized over ``semantics``, an instance of the
  typeclass ``Cava``. This instance provides implementations of circuit
  primitives, such as 1-bit logic gates. One primitive gate is a 1-bit inverter
  ``inv``, so our inverter is just a simple invocation of the primitive.

Normally, we'd write circuit definitions a little more concisely by writing them
inside a ``Section`` that contains ``signal`` and ``semantics`` as context
variables, like this:
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

  Definition inverter_concise : Circuit (signal Bit) (signal Bit)
    := Comb inv.

(*|
For the rest of the circuit definitions in this tutorial, you can assume that
we're inside the section and that every definition is parameterized over the
``signal`` and ``semantics`` context variables.

Back to our inverter. Let's take a closer look at the ``inv`` primitive.
|*)

  Check inv.

(*|
You can see in the type signature ``signal Bit -> cava (signal Bit)`` that
``inv`` is defined as a pure Coq function in terms of a monad called
``cava``. The ``cava`` monad, like ``inv``, is provided by ``semantics``. The
monad is used to capture sharing; it's semantically different in Cava to write::

  x <- inv zero ;;
  y <- inv zero ;;
  xor2 x y

than it is to write::

  x <- inv zero ;;
  xor2 x x

Both expressions have the same meaning, and if we were using Gallina ``let``
binders there would be no difference. But the generated circuit can use two
wires for the first definition, and fork the same wire in the second. As circuit
diagrams, this is the difference between::

         +-----+      +-----+
  0 -----| inv |------|     |
         +-----+      | xor |----- out
         +-----+      |     |
  0 -----| inv |------|     |
         +-----+      +-----+

and::

                        +-----+
                    +---|     |
                    |   | xor |---- out
         +-----+    |   |     |
  0 -----| inv |----+---|     |
         +-----+        +-----+

This difference isn't significant in determining what the value of ``out`` will
be, but it can be very useful when trying to exercise fine-grained control over
circuit layout and area! At a first approximation, you can think of a monadic
bind (``_ <- _ ;; ...``) as *naming a wire* in the circuit graph.

If the monad notations are unfamiliar, the reference_ has more information on
those.

We could have represented sharing by describing circuit graphs with a list of
nodes and edges. However, this is essentially the "machine code" of structural
hardware descriptions, and is far too tedious a representation for humans to
work with. The monadic-function abstraction allows human engineers to think
about the functional behavior and composition of circuits at a more intuitive
level.

Parameterizing over the ``cava`` monad and primitive implementations allows us
to use different instances of ``Cava`` to interpret the same circuit definition
in different ways. One ``Cava`` instance generates netlists by adding and
connecting wires in the background using a state monad. For circuit simulations
and proofs of functional correctness, on the other hand, we don't care about
sharing at all; these use no-op identity monad that acts the same as a ``let``
binder.

Let's use our ``inverter`` definition to see these two interpretations in
action.

.. coq:: none
|*)

End WithCava. (* end the section so we can plug in signal and semantics *)

(*|
First, let's generate a netlist. We need to define an interface that describes the
circuit's input and output ports and behavior relative to the (global) clock and
reset signals. Then we can compute a netlist (type ``CavaState``), which
describes the full layout of the circuit in a way that can be easily translated
to SystemVerilog.
|*)

(* netlist-generating semantics *)
Existing Instance CavaCombinationalNet.

Definition inverter_interface
  := sequentialInterface "inverter_interface"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" Bit]
     [mkPort "o" Bit].

Compute makeCircuitNetlist inverter_interface inverter.

(* A closer look at the circuit body *)
Compute (makeCircuitNetlist inverter_interface inverter).(module).

(*|
You may notice that we're using something called ``sequentialInterface`` here,
and referring to clock and reset signals, even though our inverter is a purely
combinational circuit. We introduce timing in the netlist interface here in
order to drive the circuit with multiple inputs over time, and to plug it in as
a subcomponent of circuits that are not combinational.

Now, let's simulate the circuit, which can be useful for testing and proving
functional correctness. Here, we use the identity-monad interpretation. The
``signal`` for this ``Cava`` instance is ``combType``, which interprets a
``Bit`` simply as a Coq ``bool``. If we provide the three inputs
``[true; false; true]`` to the circuit simulation function ``simulate``, we'll
get ``[false; true; false]``:
|*)

(* identity-monad semantics *)
Existing Instance CombinationalSemantics.

Compute simulate inverter [true; false; true].
Compute simulate inverter [true; false; true; true; true; false].

(*|
We can use the simulation to write proofs about the circuit. For instance, we
can prove that ``inverter`` obeys a natural Coq specification:
|*)

Lemma inverter_correct (input : list bool) :
  simulate inverter input = map negb input.
Proof.
  (* inline the circuit definition *)
  cbv [inverter].

  (* simplify simulate to create an expression in terms of Coq lists *)
  autorewrite with push_simulate.

  (* assert that the two List.map functions are equivalent *)
  apply map_ext. intros.

  (* inline the inv primitive (fun x => ret (negb x)) *)
  cbn [inv CombinationalSemantics].

  (* simplify the identity monad expressions *)
  simpl_ident.

  reflexivity.
Qed.

(*|
We can even prove that composing two inverters is the same as doing
nothing. Here, ``>==>`` is circuit composition (a Kleisli arrow). The proof
structure is pretty similar.
|*)

Lemma inverter_idempotent (input : list bool) :
  simulate (inverter >==> inverter) input = input.
Proof.
  cbv [inverter].
  autorewrite with push_simulate.
  rewrite map_map.
  apply List.map_id_ext. intros.
  cbn [inv CombinationalSemantics].
  simpl_ident.
  apply Bool.negb_involutive.
Qed.

(*|
A note about reading Coq proofs: in general, it's more important to understand
the lemma statement (the part before ``Proof``) than it is to understand the
proof body. The lemma statement shows what is being proven, and the proof body
contains an "argument" to Coq that the statement is true.

To summarize, there are three things you can do with Cava circuits:

1. Define them (parameterized over an abstract ``Cava`` instance)
2. Generate netlists for them using the ``CavaCombinationalNet`` instance and
   the ``makeCircuitNetlist`` function. These netlists can then be translated into
   SystemVerilog.
3. Simulate them using ``simulate``, and prove things about the simulations, by
   plugging in the ``CombinationalSemantics`` instance.

In the following examples, we'll use this exact same three-part pattern to
explore more complex circuits.

.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
Example 2 : Byte xor
====================

Our next example is a circuit that xors two bytes:
|*)

  Definition xor_byte :
    Circuit (signal (Vec Bit 8) * signal (Vec Bit 8))
            (signal (Vec Bit 8)) :=
    Comb (Vec.map2 xor2).

(*|
This circuit maps a 1-bit xor (``xor2``) over the two input vectors. ``xor2`` is
one of the primitives provided by the ``Cava`` instance, like ``inv``. Once
again, this is a combinational circuit, so we define it by wrapping a monadic
function with ``Comb``.

The ``Vec`` here is another ``SignalType``, with a slightly more complicated
construction than ``Bit``. A ``Vec Bit 8`` is a vector of 8 bits: a
byte. Vectors can be formed from any other ``SignalType``, including other
vectors; ``Vec (Vec (Vec Bit 8) 4) 2)`` is a valid construction representing a
two-dimensional array of bytes (equivalently, a three-dimensional array of
bits).

The ``Vec.map2`` definition is from Cava's vector library. It's important not to
confuse ``Vec``, the ``SignalType`` in Cava's type system, with ``Vector.t``,
Coq's standard library vector type. In simulation, ``Vec`` is translated into
``Vector.t``, so you may see both in the codebase. You can also convert back and
forth between ``Vec`` and ``Vector.t`` using the Cava primitives ``packV`` and
``unpackV``. However, Cava's vector library mirrors most of the definitions
available for Coq standard library vectors, so it's usually best to use those
definitions instead: use ``Vec.map2`` instead of ``unpackV``, ``Vector.map2``,
and ``packV``.

To see more definitions from Cava's core library, try taking a look at the Cava
reference_, which documents its contents.

.. coq:: none
|*)

End WithCava.

Local Open Scope vector_scope.

(*|
To generate a netlist for this circuit, we use mostly the same procedure as for
the inverter, except that we change the input and output port types to match the
circuit's type signature.
|*)

Definition xor_byte_interface
  := sequentialInterface "xor_byte_interface"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "v1" (Vec Bit 8); mkPort "v2" (Vec Bit 8)]
     [mkPort "o" (Vec Bit 8)].

Compute (makeCircuitNetlist xor_byte_interface xor_byte).(module).

(*|
Tuples in the input or output types become lists of ports for the netlist
interface, so ``signal (Vec Bit 8) * signal (Vec Bit 8)`` becomes ``[mkPort "v1"
(Vec Bit 8); mkPort "v2" (Vec Bit 8)]``. The names of the ports ("v1", "v2", and
"o") are just for readability and potentially for reference by other netlists;
they can be named however you prefer.

We can also, as before, simulate the circuit.
|*)

Compute
  simulate xor_byte
  [([true;  true; true;  false; false; false; false; false],
    [false; true; false; true;  false; false; false; false])].

(*|
Literal bit vectors are not especially readable, though; it's not immediately
clear that this simulation is 7 xor 10 = 13. For simulations with bitvectors,
it's often clearer to use natural-number-to-bitvector conversions from the Coq
standard library :
|*)

Compute map Bv2N
        (simulate xor_byte [(N2Bv_sized 8 7, N2Bv_sized 8 10)]).

(*|
Finally, we can prove that the circuit is correct. In this case, we prove that
the circuit's behavior matches the ``BVxor`` definition from the standard
library, specialized to bit-vectors of length 8.
|*)

Lemma xor_byte_correct (i : list (Vector.t bool 8 * Vector.t bool 8)) :
  simulate xor_byte i = map (fun '(v1,v2) => BVxor 8 v1 v2) i.
Proof.
  cbv [xor_byte]. autorewrite with push_simulate.
  apply map_ext; intros. destruct_pair_let.
  cbv [BVxor]. simpl_ident.
  apply Vector.map2_ext. reflexivity.
Qed.

(*|
Again, no need to focus too much on the body of the proof here; understanding
the lemma statement is the most important part. However, one interesting thing
to note is that the proof is not computational; we don't analyze the 2^16
possibile inputs separately. In fact, we never destruct the vectors or refer to
the length at all, which leads us to our next example.

Example 3: Bit-vector xor
=========================

As it turns out, we can define ``xor_byte`` over *arbitrary-length* bitvectors
with very little modification. The circuit is virtually identical, except that
it takes a length argument ``n`` and all the ``8``\ s are replaced with ``n``:

.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*||*)

  Definition xor_bitvec (n : nat) :
    Circuit (signal (Vec Bit n) * signal (Vec Bit n))
            (signal (Vec Bit n)) :=
    Comb (Vec.map2 xor2).

(*|
.. coq:: none
|*)

End WithCava.

(*|
We can define an interface for this circuit that also takes ``n`` as an
argument, and then compute a netlist for any number of gates we want.
|*)

Definition xor_bitvec_interface {n : nat}
  := sequentialInterface "xor_bitvec_interface"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "v1" (Vec Bit n); mkPort "v2" (Vec Bit n)]
     [mkPort "o" (Vec Bit n)].

(* Netlist for a 2-bit xor *)
Compute
  (makeCircuitNetlist xor_bitvec_interface (xor_bitvec 2)).(module).

(* Netlist for a 100-bit xor! *)
Compute
  (makeCircuitNetlist xor_bitvec_interface (xor_bitvec 100)).(module).

(*|
Simulations are the same; just plug in any size.
|*)

(* 7 xor 10 = 13 (n=8) (same as xor_byte) *)
Compute map Bv2N
        (simulate (xor_bitvec 8) [(N2Bv_sized 8 7, N2Bv_sized 8 10)]).

(* 1 xor 3 = 2 (n=2) *)
Compute map Bv2N
        (simulate (xor_bitvec 2) [(N2Bv_sized 2 1, N2Bv_sized 2 3)]).

(* 1000 xor 3 = 1003 (n=10) *)
Compute map Bv2N
        (simulate (xor_bitvec 10)
                  [(N2Bv_sized 10 1000, N2Bv_sized 10 3)]).

(*|
The correctness proof has is exactly the same as the ``xor_byte`` proof, except
with ``n`` instead of ``8``; the proof body is completely unchanged.
|*)

Lemma xor_bitvec_correct
      n (i : list (Vector.t bool n * Vector.t bool n)) :
  simulate (xor_bitvec n) i = map (fun '(v1,v2) => BVxor n v1 v2) i.
Proof.
  cbv [xor_bitvec]. autorewrite with push_simulate.
  apply map_ext; intros. destruct_pair_let.
  cbv [BVxor]. simpl_ident.
  apply Vector.map2_ext. reflexivity.
Qed.

(*|
We can also easily prove that, for 8-bit vectors, ``xor_bitvec`` is equivalent
to ``xor_byte``:
|*)

Lemma xor_bitvec_xor_byte_equiv
      (i : list (Vector.t bool 8 * Vector.t bool 8)) :
  simulate (xor_bitvec 8) i = simulate xor_byte i.
Proof. reflexivity. Qed.

(*|
This example demonstrates the advantage of using a proof assistant instead of a
more computational method. The ``xor_bitvec_correct`` proof checks essentially
instantly and holds for *all* values of ``n``. With one circuit definition, and
one proof, you have defined every single length of bit-vector xor you'll ever
need. The same principle can apply to more complicated structures as well.

Example 4: Tree of xors
=======================

.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
To take the last circuit a step further, let's consider xoring not just two
``n``-length vectors, but an arbitrary number ``m`` of ``n``-length vectors!

We could write a definition that chains the xors together one by one::

  xor (xor (xor (xor (xor a b) c) d) e f)


However, since there are no data dependencies, the circuit will have better
timing properties for possibly large ``m`` if it is a tree, e.g.::

  xor (xor (xor a b) c) (xor (xor d e) f)

Luckily, Cava's standard library contains a ``tree`` combinator for exactly this
kind of situation.
|*)

  Definition xor_tree {n m : nat} :
    Circuit (signal (Vec (Vec Bit n) m))
            (signal (Vec Bit n)) :=
    Comb (tree (Vec.map2 xor2)).

(*|
.. coq:: none
|*)

End WithCava.

(*|
Now, we can just plug in any sequence of same-size vectors and compute the
results!

One note for those less familiar with Coq: the curly braces ``{}`` around the
``n`` and ``m`` arguments are standard Coq syntax for "implicit" arguments; Coq
will try to guess their values rather than requiring them to be passed
explicitly. So we can actually write ``xor_tree vec`` instead of e.g. ``xor_tree
2 3 vec``, and Coq will try to infer ``n`` and ``m`` from the type of
``vec``. If Coq struggles to infer them, we can also plug in these arguments
manually by referencing their names, e.g. ``xor_tree (m:=3) vec``.
|*)

(* 7 xor 10 = 13 (n=8, m=2)*)
Compute map Bv2N
        (simulate xor_tree
                  [[N2Bv_sized 8 7; N2Bv_sized 8 10]]).

(* 1000 xor 3 = 1003 (n=10, m=2) *)
Compute map Bv2N
        (simulate xor_tree
                  [[N2Bv_sized 10 1000; N2Bv_sized 10 3]]).

(* 1 xor 2 xor 4 xor 8 xor 16 xor 32 xor 64 xor 128 = 255 (n=8, m=8) *)
Compute map Bv2N
        (simulate xor_tree
                  [[ N2Bv_sized 8 1
                     ; N2Bv_sized 8 2
                     ; N2Bv_sized 8 4
                     ; N2Bv_sized 8 8
                     ; N2Bv_sized 8 16
                     ; N2Bv_sized 8 32
                     ; N2Bv_sized 8 64
                     ; N2Bv_sized 8 128
                   ]]).

(*|
To prove the xor tree circuit correct, we prove that it's equivalent to a
``fold_left``, which is a native Coq loop. Essentially, this proof says that the
circuit, even with the tree structure, is equivalent to just chaining ``BVxor``
over the input in order (starting with 0, which is the identity for xor).

.. coq:: none
|*)

Hint Rewrite Nxor_BVxor using solve [eauto] : push_Bv2N.

(*||*)

Lemma xor_tree_correct n m (i : list (Vector.t (Vector.t bool n) m)) :
  m <> 0 -> (* rule out size-0 tree *)
  simulate xor_tree i = map (fun vs =>
                               Vector.fold_left
                                 (BVxor n) (N2Bv_sized n 0) vs) i.
Proof.
  cbv [xor_tree]. intros.
  autorewrite with push_simulate.
  apply map_ext; intros.

  (* this rewrite produces side conditions; we'll handle them later *)
  rewrite @tree_equiv with (t:=Vec Bit n) (id:=N2Bv_sized n 0);
    intros; auto; simpl_ident.

  { (* xor circuit is equivalent to BVxor *)
    cbv [BVxor].
    apply Vector.fold_left_ext; intros; simpl_ident.
    apply Vector.map2_ext. reflexivity. }

  (* now, solve the tree_equiv side conditions *)

  { (* 0 is a left identity *)
    apply Bv2N_inj. autorewrite with push_Bv2N.
    apply N.lxor_0_l. }
  { (* 0 is a right identity *)
    apply Bv2N_inj. autorewrite with push_Bv2N.
    apply N.lxor_0_r. }
  { (* xor is associative *)
    apply Bv2N_inj. autorewrite with push_Bv2N.
    symmetry. cbn. apply N.lxor_assoc. }
Qed.

(*|
It's worth taking a moment here again to point out just how broad the proof of
correctness is. This proof applies to a circuit that xors two bits, and also
applies to a circuit that xors 1000 1000-bit bitvectors.

As a final touch, we can also prove that, when applied to just two bitvectors
(``m = 2``), ``xor_tree`` is equivalent to ``xor_bitvec``:
|*)

Lemma xor_bitvec_xor_tree_equiv
      n (i : list (Vector.t bool n * Vector.t bool n)) :
  simulate (xor_bitvec n) i =
  simulate xor_tree (map (fun '(v1,v2) => [v1;v2]) i).
Proof.
  cbv [xor_bitvec xor_tree]; autorewrite with push_simulate.
  rewrite map_map.
  apply map_ext; intros. destruct_pair_let.

  (* The tree lemma produces the same side conditions as before, but
     we solve them here in a more concise way *)
  erewrite @tree_equiv with
      (t:=Vec Bit n) (id:=N2Bv_sized n 0)
    by (intros; auto; simpl_ident; apply Bv2N_inj;
        autorewrite with push_Bv2N;
        auto using N.lxor_0_r, N.lxor_0_l, N.lxor_assoc).

  autorewrite with push_vector_fold vsimpl. simpl_ident.
  apply Bv2N_inj. autorewrite with push_Bv2N.
  rewrite N.lxor_0_l. reflexivity.
Qed.

(*|
At this point, we've covered pretty much everything you need to start building
*combinational* circuits in Cava -- circuits that don't have any
timing-dependent elements like loops or registers. In the next example, we'll
show how to build *sequential* circuits.

Example 5 : Delay for Three Timesteps
=====================================

.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
The simplest sequential element is a unit delay (register). The delay takes in a
value at the end of the clock cycle, and then outputs the same value at the
start of the next clock cycle. So if we want to write a circuit that delays the
input stream by three timesteps, we can write three delays in a row:
|*)

  Definition three_delays {t : SignalType}
    : Circuit (signal t) (signal t) :=
    Delay >==> Delay >==> Delay.

(*|
Note that this circuit definition will delay a signal *of any type*. The ``t``
argument can be anything, although to generate a concrete netlist or simulation
it will need to be plugged in. We'll do simulations and netlist generations with
a few different types.

The ``>==>`` notation means "compose these circuits", i.e connect the output
ports of the left-hand circuit to the input ports of the second. It's short for
``Compose``, which can also be used directly.
|*)

  Locate ">==>". (* print the definition of the notation *)

  (* Exactly the same thing as three_delays, just without notation *)
  Definition three_delays_verbose {t : SignalType}
    : Circuit (signal t) (signal t) :=
    Compose (Compose Delay Delay) Delay.

(*|
.. coq:: none
|*)

End WithCava.

Local Open Scope list_scope.

(*|
``Compose`` and ``Delay`` are like ``Comb``; they are definitions that create
``Circuit``\ s. You can find a full list of ``Circuit`` constructors in the
reference_.

Here's the netlist for ``three_delays``, generated for two different signal
types:
|*)

Definition three_delays_interface {t : SignalType}
  := sequentialInterface "three_delays_interface"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" t]
     [mkPort "o" t].

(* delay a stream of bits *)
Compute
  (makeCircuitNetlist three_delays_interface
                      (three_delays (t:=Bit))).(module).

(* delay a stream of bytes *)
Compute
  (makeCircuitNetlist three_delays_interface
                      (three_delays (t:=Vec Bit 8))).(module).

(*|
Let's simulate the circuit, first using a sequence of 1s:
|*)

Compute simulate (three_delays (t:=Bit)) (repeat true 10).

(*|
You can see that we get three ``false`` outputs before getting the stream of
``true`` values. The initial state of ``Delay`` is always "zeroed out"; for a
custom initial state, you can use the alternative constructor ``DelayInit``,
which takes an initial value.

We can also simulate the circuit with bytes. To make the simulations a little
more interesting, we'll use a small convenience definition that creates a
list of bytes counting up in sequence.
|*)

(* convenience definition for a sequence of numbers as bytes *)
Definition byte_seq start len : list (combType (Vec Bit 8)) :=
  map (nat_to_bitvec_sized 8) (seq start len).

Compute map Bv2N (byte_seq 1 10). (* bytes from 1..10 *)

(*|
Now, when we run the simulations, it's easier to follow the timesteps:
|*)

Compute map Bv2N
        (simulate three_delays (byte_seq 1 10)).

(*|
We can also compose ``three_delays`` with itself to get six delays:
|*)

Compute map Bv2N
        (simulate (three_delays >==> three_delays) (byte_seq 1 10)).

(*|
Finally, the correctness proof for ``three_delays`` says that it prepends three
``defaultSignal`` values (the generic name for "a zeroed-out value of the
correct signal type") to the input, then truncates the new list to the length of
the original input.
|*)

Lemma three_delays_correct t (input : list (combType t)) :
  simulate three_delays input
  = firstn (length input)
           (defaultSignal :: defaultSignal :: defaultSignal :: input).
Proof.
  cbv [three_delays]; autorewrite with push_simulate.
  autorewrite with push_length natsimpl.
  rewrite <-!firstn_cons. rewrite !firstn_firstn.
  autorewrite with natsimpl. reflexivity.
Qed.

(*|
Example 6 : Sum the Input Stream
================================

.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
This example will introduce ``Loop``, a circuit constructor that connects the
output port of a circuit to its own input port with a delay in the middle. This
creates *internal state* values, which can be referenced from inside the loop
but are not visible outside it. Visually, a loop looks like this:

.. image:: loop.png
   :width: 70%
   :alt: Circuit diagram showing a loop.

The following circuit gets a stream of bit-vectors as input, and uses ``Loop``
to provides the rolling sum as output:
|*)

  Definition sum {n : nat}
    : Circuit (signal (Vec Bit n)) (signal (Vec Bit n)) :=
    Loop
      (* The combinational circuit that makes up the loop body *)
      (Comb
         (fun '(input, state) =>
            sum <- addN (input, state) ;;
            (* return output and new state (the same in our case) *)
            ret (sum, sum))).

(*|
The body of this loop is a combinational circuit whose input is the loop input
signal and the internal state, and whose output is the loop output signal and
the new state.

As discussed in the very first example, the ``_ <- _ ;; _`` notation is a
monadic bind; it's like a ``let`` binder or variable assignment, except that it
helps Cava track resource sharing. ``ret`` means "return". You can read in much
more detail about monad notations in the reference_.

For the purposes of the tutorial, we'll introduce just one more monad notation:
monad composition, represented by ``>=>``. Assuming ``f`` and ``g`` are monadic
functions, writing ``f >=> g`` is the same as writing ``fun x => y <- f x ;; g
y``. This is very similar to the notation for ``Compose`` (``>==>``) shown
earlier, except that it works for the bodies of combinational circuits rather
than for sequential circuits.

Using ``>=>``, we can rewrite ``sum`` as:
|*)

  (* Means exactly the same thing as sum *)
  Definition sum_concise {n : nat}
    : Circuit (signal (Vec Bit n)) (signal (Vec Bit n)) :=
    Loop (Comb (addN >=> fork2)).

(*|
The ``fork2`` combinator simply duplicates its input (like a fork in a wire).

As written, the ``sum`` and ``sum_concise`` circuits will start with an initial
state of zero (or ``defaultSignal``). If we want to pull in a specific initial
value, we can use ``LoopInit`` instead and plug in a compile-time constant:
|*)

  Definition sum_init {n : nat} (init : combType (Vec Bit n)) :=
    LoopInit init (Comb (addN >=> fork2)).

(*|
.. coq:: none
|*)

  Definition double_sum {n : nat}
    : Circuit (signal (Vec Bit n)) (signal (Vec Bit n)) :=
    sum >==> sum.

  Definition double_sum_mealy {n : nat}
    : Circuit (signal (Vec Bit n)) (signal (Vec Bit n)) :=
    Loop
      (Loop
         (Comb (fun '(v, ctr1, ctr2) =>
                  (* ctr1 += v *)
                  ctr1' <- addN (ctr1, v) ;;
                  (* ctr2 += ctr1 *)
                  ctr2' <- addN (ctr2, ctr1') ;;
                  (* output = ctr2 (also return new states of sums) *)
                  ret (ctr2', ctr1', ctr2')
      ))).

  Definition double_sum_mealy_chaining {n : nat}
    : Circuit (signal (Vec Bit n)) (signal (Vec Bit n)) :=
    Loop
      (Loop
         (Comb
            (                (* start: (v, ctr1), ctr2     *)
              first addN >=>        (* ctr1', ctr2         *)
                    first fork2 >=> (* (ctr1', ctr1'), ctr2  *)
                    pair_right >=>  (* ctr1', (ctr1', ctr2)  *)
                    second addN >=> (* ctr1', ctr2'        *)
                    swap >=>        (* ctr2', ctr1'        *)
                    first fork2 >=> (* (ctr2', ctr2'), ctr1' *)
                    pair_right >=>  (* ctr2', (ctr2', ctr1') *)
                    swap            (* (ctr2', ctr1'), ctr2' *)
      ))).

(*|
.. coq:: none
|*)

End WithCava.

(* same as sum of 1..10 *)
Compute map Bv2N
        (simulate double_sum (repeat (N2Bv_sized 8 1) 10)).

(*|
Here's the netlist for ``sum``. You can see that no "loop" appears in the final
version, just a delay connecting the loop's output to its own input.
|*)

Definition sum_interface {n : nat}
  := sequentialInterface "sum_interface"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" (Vec Bit n)]
     [mkPort "o" (Vec Bit n)].

Compute
  (makeCircuitNetlist sum_interface (sum (n:=8))).(module).

(*|
The netlist for ``sum_init`` can use the same interface, but needs an extra
argument for the initial value:
|*)

Compute
  (makeCircuitNetlist sum_interface
                      (sum_init (N2Bv_sized 8 10))).(module).

(*|
Let's run a few simulations to see the circuit in action:
|*)

(* sum of 10 1s = 1,2,3,...10 *)
Compute map Bv2N
        (simulate sum (repeat (N2Bv_sized 8 1) 10)).

(* sum of 1..10 = 1, 3, 6, 10, 15, 21, 28, 36, 45, 55 *)
Compute map Bv2N
        (simulate sum (byte_seq 1 10)).

(* sum of 10 1s starting at 10 = 11,12,13,...20 *)
Compute map Bv2N
        (simulate (sum_init (N2Bv_sized 8 10))
                  (repeat (N2Bv_sized 8 1) 10)).

(*|
To write a correctness proof for ``sum``, we first need to describe its
behavior. There are many ways to do this, but one way is shown below.
|*)

(* computes the sum of a list of numbers (as a single number, not the
   rolling sum) *)
Definition sum_list_N (input : list N) : N :=
  fold_left N.add input 0%N.

(* computes the *rolling* sum; the nth element of the output represents
   the sum of the input up to index n *)
Definition rolling_sum (input : list N) : list N :=
  map (fun i => sum_list_N (firstn (S i) input)) (seq 0 (length input)).

(* example to show the behavior of rolling_sum *)
Compute rolling_sum [5;6;7]%N.

(* specification for the sum circuit : convert to N, get rolling_sum,
   convert back to bit-vectors *)
Definition spec_of_sum {n} (input : list (combType (Vec Bit n)))
  : list (combType (Vec Bit n))
  := map (N2Bv_sized n) (rolling_sum (map Bv2N input)).

(*|
To reason about loops, we can use loop-invariant lemmas like this one:
|*)

Check simulate_Loop_invariant.

(*|
To use the loop-invariant lemma, though, we need to figure out what the
invariant of ``sum`` should be. The invariant of a loop takes four arguments:
the timestep (a ``nat``), the current loop state (i.e. the value held by the
delay at this timestep), the state of the loop-body circuit, and the output
accumulator (a list of the outputs generated so far). Because the ``sum``
circuit has a purely combinational body, it has no internal state, so the body
state in our case is just Coq's ``unit`` type. Here's the invariant statement:
|*)

Definition sum_invariant {n} (input : list (combType (Vec Bit n)))
           (t : nat)
           (loop_state : combType (Vec Bit n))
           (body_circuit_state : unit)
           (output_accumulator : list (combType (Vec Bit n))) : Prop :=
  (* at timestep t... *)
  (* ...the loop state holds the sum of the inputs so far (that is,
     the first t inputs) *)
  loop_state = N2Bv_sized n (sum_list_N (map Bv2N (firstn t input)))
  (* ... and the output accumulator matches the rolling-sum spec
     applied to the inputs so far *)
  /\ output_accumulator = spec_of_sum (firstn t input).

(*|
Now, we can use the invariant to prove a correctness lemma. This proof could
certainly be a little more elegant and automated, but the steps are left
explicit here for those who are curious to follow the reasoning in detail.
|*)

(* This lemma is helpful for sum_correct *)
Lemma sum_list_N_snoc_bitvec n l (v : Vector.t bool n) :
  N2Bv_sized n (sum_list_N (l ++ [Bv2N v]))
  = N2Bv_sized n (Bv2N v + Bv2N (N2Bv_sized n (sum_list_N l)))%N.
Proof.
  cbv [sum_list_N]. autorewrite with pull_snoc.
  (* use Bv2N to bring the goal into the N realm, where it's
     easier to solve using modular arithmetic rules *)
  bitvec_to_N.
  rewrite N.add_mod_idemp_r by (apply N.pow_nonzero; lia).
  rewrite N.add_comm.
  reflexivity.
Qed.

(* Correctness lemma for sum *)
Lemma sum_correct n (input : list (combType (Vec Bit n))):
  simulate sum input = spec_of_sum input.
Proof.
  cbv [sum].
  (* apply loop invariant lemma using sum_invariant; generates three
     side conditions *)
  apply simulate_Loop_invariant with
      (body:=Comb _) (I:=sum_invariant input).

  { (* prove that invariant holds at the start of the loop *)
    cbv [sum_invariant]. cbn.
    split; reflexivity. }

  { (* prove that, if the invariant holds at the beginning of the loop
       body for timestep t, it holds at the end of the loop body for
       timestep t + 1 *)
    cbv [sum_invariant step]. intros. simpl_ident.
    logical_simplify; subst.
    split. (* separate the two invariant clauses *)

    { (* prove loop_state has the correct value *)
      rewrite firstn_succ_snoc with (d0:=d) by lia.
      autorewrite with pull_snoc.
      rewrite sum_list_N_snoc_bitvec.
      reflexivity. }

    { (* prove the output accumulator has the correct value *)
      cbv [spec_of_sum rolling_sum].
      (* simplify expression using list lemmas *)
      rewrite !map_map.
      autorewrite with push_length natsimpl.
      rewrite firstn_succ_snoc with (d0:=d) by lia.
      autorewrite with pull_snoc natsimpl.
      apply f_equal2. (* split front of lists from last elements *)
      { apply map_ext_in; intro.
        rewrite in_seq; intros.
        autorewrite with push_firstn push_length natsimpl listsimpl.
        reflexivity. }
      { autorewrite with push_firstn push_length natsimpl listsimpl.
        rewrite sum_list_N_snoc_bitvec. reflexivity. } } }

  { (* prove that the invariant implies the postcondition *)
    cbv [sum_invariant]; intros.
    logical_simplify; subst.
    autorewrite with push_firstn.
    reflexivity. }
Qed.

(*|
To wrap up our ``sum`` proofs, here's a quick demonstration that ``sum_concise``
is equivalent to ``sum``:
|*)

Lemma sum_concise_correct n (input : list (combType (Vec Bit n))):
  simulate sum_concise input = simulate sum input.
Proof. reflexivity. Qed.

(*|
Example 7 : Fibonacci Sequence
==============================

.. coq:: none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
In this example, we'll write a circuit that computes the Fibonacci
sequence. Here's the circuit diagram:

.. image:: fibonacci.png
   :width: 70%
   :alt: Circuit diagram for the fibonacci circuit

In the diagram, ``r1`` and ``r2`` are registers. Because of the delay a register
introduces, the ``addN`` in the middle of the circuit will, at timestep ``t``,
add together the output from timestep ``t-1`` and the output from timestep
``t-2``. In Cava, the circuit description looks like:
|*)

  Definition fibonacci {sz}
    : Circuit (signal Void) (signal (Vec Bit sz)) :=
    (* initial state of r1 = 1 *)
    let r1_init : combType (Vec Bit sz) := N2Bv_sized sz 1 in
    (* initial state of r2 = 2^sz-1 *)
    let r2_init : combType (Vec Bit sz) :=
        N2Bv_sized sz (2^N.of_nat sz - 1) in

    LoopInit r1_init
             ( (* start: (in, r1) *)
               Comb (dropl >=> fork2) >==> (* r1, r1 *)
                    Second (DelayInit r2_init) >==> (* r1, r2 *)
                    Comb (addN >=> fork2) (* r1 + r2, r1 + r2 *)).

(*|
Note the initial values. In order to get the correct output for the first two
timesteps (0 and 1), we set ``r1 = 1`` and ``r2 = 2^sz-1``, where ``sz`` is the
size of the bit vector. Since ``addN`` performs truncating bit-vector addition,
the two initial values will sum to zero.

The circuit input is a ``Void`` signal, another ``SignalType``. It's an empty
type that's interpreted as a ``unit`` in Coq, and only serves to tell the
circuit how many timesteps it should run for.

It's also possible to write the ``fibonacci`` circuit as two nested loops with a
combinational body (essentially a mealy_ machine).
|*)

  Definition fibonacci_mealy {sz}
    : Circuit (signal Void) (signal (Vec Bit sz)) :=
    let v1 : combType (Vec Bit sz) := N2Bv_sized sz 1 in
    let v_negative1 : combType (Vec Bit sz) := Vector.const one sz in
    LoopInit v1
      (LoopInit v_negative1
                (Comb
                   (fun '(_,r1,r2) =>
                      sum <- addN (r1, r2) ;;
                      ret (sum, sum, r1)))).

(*|
.. coq:: none
|*)

End WithCava.

(*|
As always, we can generate a netlist:
|*)

Definition fibonacci_interface {n : nat}
  := sequentialInterface "sum_interface"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" Void]
     [mkPort "o" (Vec Bit n)].

Compute
  (makeCircuitNetlist fibonacci_interface
                      (fibonacci (sz:=4))).(module).

Compute
  (makeCircuitNetlist fibonacci_interface
                      (fibonacci_mealy (sz:=4))).(module).

(*|
We can run some simulations to make sure the circuit produces the expected
outputs:
|*)

Compute map Bv2N
        (simulate (fibonacci (sz:=8)) (repeat tt 10)).

Compute map Bv2N
        (simulate (fibonacci_mealy (sz:=8)) (repeat tt 10)).

(*|
Let's now try to prove that the circuit is correct. As with ``sum``, we first
need to first describe the behavior we expect. Here's a natural-number function
that computes the nth element of the Fibonacci sequence:
|*)

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

(*|
So, the specification of our ``fibonacci`` circuit is that, given ``n`` of its
empty inputs, the circuit produces (the bit-vector versions of) the first ``n``
elements of the Fibonacci sequence:
|*)

Definition spec_of_fibonacci {sz} (input : list unit)
  : list (combType (Vec Bit sz))
  := map (fun n => N2Bv_sized sz (N.of_nat (fibonacci_nat n)))
         (seq 0 (length input)).

(*|
We'll need a loop invariant, which just says that the output accumulator matches
the spec and that the values in ``r1`` and ``r2`` are the right numbers from the
Fibonacci sequence.
|*)

Definition fibonacci_invariant {sz}
           (t : nat)
           (loop_state : combType (Vec Bit sz))
           (body_circuit_state :
              unit * (unit * combType (Vec Bit sz)) * unit)
           (output_accumulator : list (combType (Vec Bit sz))) : Prop :=
  let r1 := loop_state in
  let r2 := snd (snd (fst body_circuit_state)) in
  (* at timestep t... *)
  (* ...r1 holds fibonacci_nat (t-1), or 1 if t=0 *)
  r1 = match t with
       | 0 => N2Bv_sized sz 1
       | S t_minus1 => N2Bv_sized sz (N.of_nat (fibonacci_nat t_minus1))
       end
  (* ... and r2 holds fibonacci_nat (t-2), or 1 if t=1, 2^sz-1 if t=0 *)
  /\ r2 = match t with
         | 0 => N2Bv_sized sz (2^N.of_nat sz - 1)
         | 1 => N2Bv_sized sz 1
         | S (S t_minus2) =>
           N2Bv_sized sz (N.of_nat (fibonacci_nat t_minus2))
         end
  (* ... and the output accumulator matches the circuit spec for the
     inputs so far *)
  /\ output_accumulator = spec_of_fibonacci (repeat tt t).

(*|
Note that, unlike for ``sum``, there's actually a bit-vector
in the loop body state from the ``DelayInit`` element.

The extra ``unit`` types are an unfortunate feature of the current setup and
we're working on removing them. For now, just know that you can figure out what
the loop body's type should be by computing its ``circuit_state``, like this:
|*)

Compute (circuit_state
           (* body of fibonacci loop: *)
           (Comb (dropl >=> fork2) >==>
                 Second (DelayInit _) >==>
                 Comb (addN >=> fork2))).

(*|
Here's the proof of correctness, with the help of a couple of small
helper lemmas:
|*)

(* Helper lemma for fibonacci_correct *)
Lemma bitvec_negative_one_plus_one sz :
  N2Bv_sized sz (1 + (2^N.of_nat sz - 1)) = N2Bv_sized sz 0.
Proof.
  bitvec_to_N.
  assert (2^N.of_nat sz <> 0)%N by (apply N.pow_nonzero; lia).
  transitivity ((2^N.of_nat sz) mod (2 ^ N.of_nat sz))%N;
    [ f_equal; lia | ].
  rewrite N.mod_same, N.mod_0_l by lia.
  reflexivity.
Qed.

(* Helper lemma for fibonacci_correct *)
Lemma fibonacci_nat_step n :
  fibonacci_nat (S (S n)) = fibonacci_nat (S n) + fibonacci_nat n.
Proof. cbn [fibonacci_nat]. lia. Qed.

(* the nth element of the simulation output is the bit-vector version of
   (fibonacci_spec n) *)
Lemma fibonacci_correct sz (input : list unit) :
  simulate (fibonacci (sz:=sz)) input = spec_of_fibonacci input.
Proof.
  cbv [fibonacci]. autorewrite with simpl_ident.

  (* TODO(jadep): shouldn't need to specify body:= here *)
  eapply simulate_LoopInit_invariant
    with
      (body:=Comb _ >==>
                  Second (DelayInit (t:=Vec Bit sz) _) >==> Comb _)
      (I:=fibonacci_invariant).

  { (* prove loop invariant holds at start *)
    cbv [fibonacci_invariant]. cbn.
    ssplit; reflexivity. }

  { (* prove that, if the invariant holds at the beginning of the loop
       body for timestep t, it holds at the end of the loop body for
       timestep t + 1 *)
    cbv [fibonacci_invariant DelayInit mcompose].
    cbn [circuit_state step]. intros; simpl_ident.
    destruct_products. cbn [fst snd] in *.
    logical_simplify; subst.
    cbv [spec_of_fibonacci].
    autorewrite with push_length.
    destruct t; [ | destruct t ].

    { (* t = 0 case *)
      cbn [seq map fibonacci_nat].
      autorewrite with pull_N2Bv_sized.
      rewrite bitvec_negative_one_plus_one.
      ssplit; reflexivity. }

    { (* t = 1 case *)
      cbn [seq map fibonacci_nat].
      autorewrite with pull_N2Bv_sized.
      ssplit; reflexivity. }

    { (* t >= 2 *)
      autorewrite with pull_snoc natsimpl pull_N2Bv_sized.
      rewrite fibonacci_nat_step.
      ssplit; repeat (f_equal; try lia). } }

  { (* prove that the invariant implies the postcondition *)
    cbv [fibonacci_invariant]; intros.
    logical_simplify; subst. cbn [combType].
    rewrite <-(list_unit_equiv input).
    reflexivity. }
Qed.

(*|
That concludes our tutorial! If you want to explore further, take a look at the
``examples`` directory in our GitHub repo_. You can also view the full source_
for this page if you want to experiment with these examples yourself.

.. _Alectryon: https://github.com/cpitclaudel/alectryon
.. _reference: ../reference
.. _mealy: https://en.wikipedia.org/wiki/Mealy_machine
.. _repo: https://github.com/project-oak/silveroak
.. _source: https://github.com/project-oak/silveroak/blob/main/demos/tutorial.v
|*)
