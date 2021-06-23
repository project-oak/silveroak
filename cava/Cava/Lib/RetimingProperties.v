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
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Loopless.
Require Import Cava.Semantics.LooplessProperties.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Semantics.WeakEquivalence.
Require Import Cava.Lib.CircuitTransforms.
Require Import Cava.Lib.CircuitTransformsProperties.
Require Import Cava.Lib.Retiming.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Import ListNotations Circuit.Notations MonadNotation.

(* Start from scratch again. What do we really need? *)

(*
All should be based on phase_retimed!
- Move input delays over compose
- Move state delays over feedback
- Add delays to one end or the other, increment retiming number
- retimed 0 0 <-> cequiv
- Move delays over compose for loop-free circuits in general?
- Move delays in/out of loops?

 *)

Lemma move_delays {i o} (c : Circuit i o) :
  is_loop_free c = true -> wequiv (delays >==> c) (c >==> delays).
Admitted.

Lemma split_ndelays {t1 t2} n :
  wequiv (ndelays (t:=t1 * t2) n) (Par (ndelays n) (ndelays n)).
Admitted.

Lemma ndelays_First {t1 t2 o1} (f : Circuit _ o1) n :
  wequiv (ndelays (t:=t1 * t2) n >==> First f)
         (Par (ndelays n >==> f) (ndelays n)).
Admitted.

Lemma delay1_input {i o} n m (c1 c2 : Circuit i o) :
  phase_retimed n m c1 (delays >==> c2) ->
  phase_retimed n (S m) c1 c2.
Admitted.

Lemma delayn_input {i o} n m (c1 c2 : Circuit i o) :
  phase_retimed n 0 c1 (ndelays m >==> c2) ->
  phase_retimed n m c1 c2.
Admitted.

Instance phase_retimed_0_refl {i o} : Reflexive (@phase_retimed i o 0 0) | 10.
Proof.
  intro c. cbv [phase_retimed]. exists id, id. split; [ reflexivity | ].
  change (Comb (semantics:=CombinationalSemantics) (@id (value (loops_state c))))
    with (Id (t:=loops_state c)).
  autorewrite with circuitsimplw. reflexivity.
Qed.

Axiom reassemble_state :
  forall {i o} (c : Circuit i o), value (circuit_state (loopless c)) -> value (loops_state c) -> value (circuit_state c).

Axiom loops_state_from_circuit_state :
  forall {i o} (c : Circuit i o), value (circuit_state c) -> value (loops_state c).

Global Instance Proper_phase_retimed {i o} :
  Proper (eq ==> eq ==> wequiv ==> wequiv ==> iff) (@phase_retimed i o).
Proof.
  repeat intro. subst.
  split; cbv [phase_retimed]; intros; logical_simplify.
Admitted.

Require Import Coq.derive.Derive.

Local Ltac simpl_resets :=
  cbn [step fst snd defaultValue default_value
            CombinationalSemantics defaultSignal defaultCombValue].

Derive pipelined_nand
       SuchThat (phase_retimed
                   0 2 pipelined_nand
                   (Comb (i:=Bit*Bit) (o:=Bit) and2
                         >==> Comb (o:=Bit) inv))
       As pipelined_nand_correct.
Proof.
  (* insert a delay *)
  apply delay1_input.
  (* move the delay to the end of the circuit *)
  rewrite move_delays by reflexivity.
  (* insert another delay *)
  apply delay1_input.
  (* move the delay in between the and2 and inv *)
  rewrite !Compose_assoc_w.
  rewrite move_delays by reflexivity.
  (* reflexivity *)
  subst pipelined_nand. reflexivity.
Qed.
Print pipelined_nand.
Check pipelined_nand_correct.

Definition cipher_middle_round
           {state key : type}
           (sbytes : Circuit state state)
           (shrows : Circuit state state)
           (mxcols : Circuit state state)
           (add_rk : Circuit (state * key) state)
  : Circuit (state * key) state :=
  First (sbytes >==> shrows >==> mxcols) >==> add_rk.

Derive retimed_cipher_middle_round
       SuchThat
       (forall {state key} n
          (sbytes retimed_sbytes shrows mxcols : Circuit state state)
          (add_rk : Circuit (state * key) state),
           phase_retimed 0 n retimed_sbytes sbytes ->
           phase_retimed
             0 n
             (retimed_cipher_middle_round
                state key retimed_sbytes shrows mxcols add_rk)
             (cipher_middle_round sbytes shrows mxcols add_rk))
       As retimed_cipher_middle_round_correct.
Proof.
  intros. cbv [cipher_middle_round].
  autorewrite with circuitsimplw.
  eapply delayn_input.
  cbv [phase_retimed] in * |- . logical_simplify.
  destruct_lists_by_length. cbn [ndelays] in *.
  cbv [Par] in *; autorewrite with circuitsimplw in *.
  rewrite ndelays_First.

  (* TODO: not quite working right now, how to properly incorporate retimed
     subcomponents? *)
Abort.
