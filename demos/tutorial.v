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
with Coq syntax. Use Ctrl+down and Ctrl+up to step through the Coq code along
with the tutorial.

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

Compute (makeCircuitNetlist inverter_interface inverter).

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

Compute (simulate inverter [true; false; true]).
Compute (simulate inverter [true; false; true; true; true; false]).

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
the lemma statement (the part before ``Proof`` than it is to understand the
proof body. The lemma statement shows what is being proven, and the proof body
contains an "argument" to Coq that the statement is true.

To summarize, there are three things you can do with Cava circuits:

1. Define them (parameterized over an abstract ``Cava`` instance)
2. Generate netlists for them using the ``CavaCombinationalNet`` instance and
   the ``makeCircuitNetlist`` function. These netlists can then be translated into
   SystemVerilog.
3. Simulate them using ``simulate``, and prove things about the simulations, by
   plugging in the ``CombinationalSemantics`` instance.

In the next example, we'll try a slightly more complex circuit.

coq::none
|*)

Section WithCava.
  Context {signal} {semantics : Cava signal}.

(*|
Example 2 : Bit-vector xor
==========================
More than 2?
|*)

  Definition xor_byte :
    Circuit (signal (Vec Bit 8) * signal (Vec Bit 8))
            (signal (Vec Bit 8)) :=
    Comb (fun '(v1, v2) => Vec.map2 xor2 v1 v2).

  Definition xor_bitvec {n : nat} :
    Circuit (signal (Vec Bit n) * signal (Vec Bit n))
            (signal (Vec Bit n)) :=
    Comb (fun '(v1, v2) => Vec.map2 xor2 v1 v2).

  Definition xor_tree {n m : nat} :
    Circuit (signal (Vec (Vec Bit n) m))
            (signal (Vec Bit n)) :=
    Comb (tree (fun '(v1, v2) => Vec.map2 xor2 v1 v2)).

(*|
coq::none
|*)

End WithCava.

(*|
Simulations
|*)

Compute (simulate xor_byte [([true; true; true; false; false; false; false; false]%vector,
                             [false; true; false; true; false; false; false; false]%vector)]).

Compute (map Bv2N (simulate xor_byte [(N2Bv_sized 8 7, N2Bv_sized 8 10)])).

Compute (map Bv2N (simulate xor_bitvec [(N2Bv_sized 8 7, N2Bv_sized 8 10)])).
Compute (map Bv2N (simulate xor_bitvec [(N2Bv_sized 2 1, N2Bv_sized 2 3)])).
Compute (map Bv2N (simulate xor_bitvec [(N2Bv_sized 10 1000, N2Bv_sized 10 3)])).

Compute (map Bv2N (simulate xor_tree [[N2Bv_sized 8 7; N2Bv_sized 8 10]%vector])).
Compute (map Bv2N (simulate xor_tree [[N2Bv_sized 2 1; N2Bv_sized 2 3]%vector])).
Compute (map Bv2N (simulate xor_tree [[N2Bv_sized 10 1000; N2Bv_sized 10 3]%vector])).
Compute (map Bv2N (simulate xor_tree
                            [[ N2Bv_sized 8 1
                               ; N2Bv_sized 8 2
                               ; N2Bv_sized 8 4
                               ; N2Bv_sized 8 8
                               ; N2Bv_sized 8 16
                               ; N2Bv_sized 8 32
                               ; N2Bv_sized 8 64
                               ; N2Bv_sized 8 128
                             ]%vector])).

(*|
Proofs
|*)

Lemma xor_byte_correct (i : list (Vector.t bool 8 * Vector.t bool 8)) :
  simulate xor_byte i = map (fun '(v1,v2) => Bvector.BVxor 8 v1 v2) i.
Proof.
  cbv [xor_byte]. autorewrite with push_simulate.
  apply map_ext; intros.
  repeat destruct_pair_let. (* get rid of let '(_,_) pattern *)
  cbv [Bvector.BVxor]. simpl_ident.
  apply Vector.map2_ext. reflexivity.
Qed.

Lemma xor_bitvec_correct n (i : list (Vector.t bool n * Vector.t bool n)) :
  simulate xor_bitvec i = map (fun '(v1,v2) => Bvector.BVxor n v1 v2) i.
Proof.
  cbv [xor_bitvec]. autorewrite with push_simulate.
  apply map_ext; intros. destruct_pair_let.
  cbv [Bvector.BVxor]. simpl_ident.
  apply Vector.map2_ext. reflexivity.
Qed.

Lemma xor_bitvec_xor_byte_equiv (i : list (Vector.t bool 8 * Vector.t bool 8)) :
  simulate xor_bitvec i = simulate xor_byte i.
Proof. reflexivity. Qed.

(*|
coq::none
|*)
Hint Rewrite Nxor_BVxor using solve [eauto] : push_Bv2N.

(*|
|*)

Lemma xor_tree_correct n m (i : list (Vector.t (Vector.t bool n) m)) :
  m <> 0 -> (* rule out size-0 tree *)
  simulate xor_tree i = map (fun vs =>
                               Vector.fold_left
                                 (Bvector.BVxor n) (N2Bv_sized n 0) vs) i.
Proof.
  cbv [xor_tree]. intros.
  autorewrite with push_simulate.
  apply map_ext; intros.
  apply (tree_equiv (t:=Vec Bit n)); intros; auto.
  { (* 0 is a left identity *)
    apply Bv2N_inj. autorewrite with push_Bv2N.
    apply N.lxor_0_l. }
  { (* 0 is a right identity *)
    apply Bv2N_inj. autorewrite with push_Bv2N.
    apply N.lxor_0_r. }
  { (* xor is associative *)
    apply Bv2N_inj. autorewrite with push_Bv2N.
    symmetry. apply N.lxor_assoc. }
  { (* xor circuit is equivalent to BVxor *)
    cbv [Bvector.BVxor]. simpl_ident.
    apply Vector.map2_ext. reflexivity. }
Qed.

Check xor_tree_correct 1000 1000.

Lemma xor_bitvec_xor_tree_equiv n (i : list (Vector.t bool n * Vector.t bool n)) :
  simulate xor_bitvec i = simulate xor_tree
                                   (map (fun '(v1,v2) => [v1;v2]%vector) i).
Proof.
  cbv [xor_bitvec xor_tree]; autorewrite with push_simulate.
  rewrite map_map.
  apply map_ext; intros. destruct_pair_let.

  (* The tree lemma produces the same side conditions as before, but we solve
     them here in a more concise way *)
  erewrite @tree_equiv with
      (t:=Vec Bit n) (op:=Bvector.BVxor n) (id:=N2Bv_sized n 0)
    by (intros; auto; simpl_ident; apply Bv2N_inj; autorewrite with push_Bv2N;
        auto using N.lxor_0_r, N.lxor_0_l, N.lxor_assoc).

  autorewrite with push_vector_fold vsimpl. simpl_ident.
  apply Bv2N_inj. autorewrite with push_Bv2N.
  rewrite N.lxor_0_l. reflexivity.
Qed.
