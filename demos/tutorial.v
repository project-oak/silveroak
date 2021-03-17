(*|
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

Welcome! This is a quick primer for designing circuits with Cava. We'll walk
through a few small examples end-to-end. This tutorial will not explain Coq
syntax in depth, but will use the same few patterns throughout; you shouldn't
need to know Coq to follow along.

Use Ctrl+down and Ctrl+up to step through the Coq code along with the
tutorial. Use Ctrl+click to focus on a particular line.

.. coq:: none
|*)

Require Import Cava.Cava.
Require Import Cava.CavaProperties.
Import Circuit.Notations.

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

  About inv.

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
     [mkPort "o" Bit]
     [].

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
     [mkPort "o" (Vec Bit 8)]
     [].

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
     [mkPort "o" (Vec Bit n)]
     [].

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

Luckily, Cava's standard library (which you can import with ``Require Import
Cava.Cava``) contains a ``tree`` combinator for exactly this kind of situation.
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
|*)

(* 7 xor 10 = 13 (n=8, m=2)*)
Compute map Bv2N
        (simulate xor_tree
                  [[N2Bv_sized 8 7; N2Bv_sized 8 10]]).

(* 1000 xor 3 = 1003 (n=10, m=2) *)
Compute map Bv2N
        (simulate (xor_bitvec 10)
                  [(N2Bv_sized 10 1000, N2Bv_sized 10 3)]).

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

Example 5 : Counter
===================

To be continued!
|*)
