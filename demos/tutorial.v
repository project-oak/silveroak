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
through a few small examples end-to-end.

.. coq:: none
|*)

Require Import ExtLib.Structures.Monads.
Import MonadNotation.
Open Scope monad_scope.

Require Import Cava.Acorn.Acorn.

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
  1 ---- | inv |------|     |
         +-----+      | xor | ---- out
         +-----+      |     |
  1 ---- | inv | ---- |     |
         +-----+      +-----+

and::

                            +-----+
                     +----- |     |
                     |      | xor | ---- out
         +-----+     |      |     |
  1 ---- | inv | ----+----- |     |
         +-----+            +-----+

This difference isn't significant in determining what the value of ``out`` will
be, but it can be very useful when trying to exercise fine-grained control over
circuit layout and area!

Parameterizing over the ``cava`` monad and primitive implementations allows us
to use different instances of ``Cava`` to interpret the same circuit definition
in different ways. For instance, one ``Cava`` instance creates a netlist from
the circuit definition by using a state monad that adds and connects wires in
the background. Defining a purely combinational circuit is simply defining a
Gallina function in terms of the ``cava`` monad and ``SignalType``.

.. coq:: none
|*)

  Definition test1 : cava (signal Bit) :=
    x <- inv one ;;
    xor2 (x, x).
  Definition test2 : cava (signal Bit) :=
    x <- inv one ;;
    y <- inv one ;;
    xor2 (x, y).
End WithCava.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Cava.Cava.

Definition test_interface
  := sequentialInterface "test_interface"
     "clk" PositiveEdge "rst" PositiveEdge
     [mkPort "i" Void]
     [mkPort "o" Bit]
     [].

(* does Circuit need an input type? or can it have just one type with function applications? *)


Require Import Coq.NArith.NArith.

Compute (makeCircuitNetlist test_interface (Comb (fun _ => test1))).
(*      = {| *)
(*   netNumber := 2; *)
(*   vectorNumber := 0; *)
(*   vectorDeclarations := []; *)
(*   externalDeclarations := []; *)
(*   clockNet := Some (NamedWire "clk"); *)
(*   clockEdge := PositiveEdge; *)
(*   resetNet := Some (NamedWire "rst"); *)
(*   resetEdge := PositiveEdge; *)
(*   module := {| *)
(*             moduleName := "test_interface"; *)
(*             netlist := [AssignSignal (NamedWire "o") (Wire 1); *)
(*                        Xor (Wire 0) (Wire 0) (Wire 1);  *)
(*                        Not Vcc (Wire 0)]; *)
(*             inputs := [{| port_name := "rst"; port_type := Bit |}; *)
(*                       {| port_name := "clk"; port_type := Bit |}]; *)
(*             outputs := [{| port_name := "o"; port_type := Bit |}] |}; *)
(*   libraryModules := [] |} *)
(* : CavaState *)


Compute (makeCircuitNetlist test_interface (Comb (fun _ => test2))).
(* = {| *)
(*   netNumber := 3; *)
(*   vectorNumber := 0; *)
(*   vectorDeclarations := []; *)
(*   externalDeclarations := []; *)
(*   clockNet := Some (NamedWire "clk"); *)
(*   clockEdge := PositiveEdge; *)
(*   resetNet := Some (NamedWire "rst"); *)
(*   resetEdge := PositiveEdge; *)
(*   module := {| *)
(*             moduleName := "test_interface"; *)
(*             netlist := [AssignSignal (NamedWire "o") (Wire 2); *)
(*                        Xor (Wire 0) (Wire 1) (Wire 2);  *)
(*                        Not Vcc (Wire 1); Not Vcc (Wire 0)]; *)
(*             inputs := [{| port_name := "rst"; port_type := Bit |}; *)
(*                       {| port_name := "clk"; port_type := Bit |}]; *)
(*             outputs := [{| port_name := "o"; port_type := Bit |}] |}; *)
(*   libraryModules := [] |} *)
(* : CavaState *)
