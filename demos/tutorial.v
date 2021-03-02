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
through a few small examples end-to-end. This tutorial assumes some familiarity
with Coq syntax. Use Ctrl+down and Ctrl+up to step through the Coq code along with the tutorial.

.. coq:: none
|*)

Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.StateMonad.
Import ListNotations MonadNotation.
Open Scope monad_scope.

Require Import Cava.Cava.
Require Import Cava.ListUtils.
Require Import Cava.Acorn.Acorn.
Require Import Cava.Acorn.Identity.
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
  primitives, such as 1-bit logic gates. One primitive is a 1-bit inverter
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
monad is used to preserve sharing; it's semantically different in Cava to write::

  x <- inv zero ;;
  y <- inv zero ;;
  xor2 x y

than it is to write::

  x <- inv zero ;;
  xor2 x x

Both expressions have the same meaning, and if we were using Gallina ``let``
binders there would be no difference. But the generated circuit will use two
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

Compute (makeCircuitNetlist inverter_interface inverter).

(* A closer look at the circuit body *)
Compute (makeCircuitNetlist inverter_interface inverter).(module).

(*|
Now, let's simulate the circuit, which can be useful for testing and proving
functional correctness. Here, we use the identity-monad interpretation. The
``signal`` for this ``Cava`` instance is ``combType``, which interprets a
``Bit`` simply as a Coq ``bool``. If we provide the three inputs
``[true; false; true]`` to the circuit simulation function ``multistep``, we'll
get ``[false; true; false]``:
|*)

(* identity-monad semantics *)
Existing Instance CombinationalSemantics.

Compute (multistep inverter [true; false; true]).
Compute (multistep inverter [true; false; true; true; true; false]).

(*|
We can use the simulation to write proofs about the circuit. For instance, we
can prove that ``inverter`` obeys a natural Coq specification:
|*)

Lemma inverter_correct (input : list bool) :
  multistep inverter input = map negb input.
Proof.
  (* inline the circuit definition *)
  cbv [inverter].

  (* simplify multistep to create an expression in terms of Coq lists *)
  autorewrite with push_multistep.

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
  multistep (inverter >==> inverter) input = input.
Proof.
  cbv [inverter].
  autorewrite with push_multistep.
  rewrite map_map.
  apply map_id_ext. intros.
  cbn [inv CombinationalSemantics].
  simpl_ident.
  apply Bool.negb_involutive.
Qed.

(*|
To summarize, there are three things you can do with Cava circuits:

1. Define them (parameterized over an abstract ``Cava`` instance)
2. Generate netlists for them using the ``CavaCombinationalNet`` instance and
   the ``makeCircuitNetlist`` function. These netlists can then be translated into
   SystemVerilog.
3. Simulate them using ``multistep``, and prove things about the simulations, by
   plugging in the ``CombinationalSemantics`` instance.

In the next example, we'll try a slightly more complex circuit.

Example 2 : 8-Bit xor
=====================

To be continued!
|*)
