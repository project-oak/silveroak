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
Require Import Cava.Semantics.Simulation.
Require Import Cava.Semantics.WeakEquivalence.
Require Import Cava.Lib.CircuitTransforms.
Require Import Cava.Lib.CircuitTransformsProperties.
Require Import Cava.Lib.Retiming.
Require Import Cava.Lib.Multiplexers.
Require Import Cava.Lib.MultiplexersProperties.
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

Lemma LoopInit_ignore_state {i o s} resetval (c : Circuit i o) :
  cequiv (LoopInit (s:=s) resetval (First c)) c.
Proof.
  exists (fun s1 s2 => fst (snd s1) = s2). cbn [circuit_state LoopInit value].
  split; [ reflexivity | ].
  intros; destruct_products; cbn [fst snd] in *; subst.
  cbn [step LoopInit]. simpl_ident.
  repeat (destruct_pair_let; cbn [fst snd]).
  split; reflexivity.
Qed.

Lemma LoopInit_merge {i1 o1 o2 s1 s2} r1 r2
      (c1 : Circuit (i1 * s1) (o1 * s1))
      (c2 : Circuit (o1 * s2) (o2 * s2)) :
  cequiv (LoopInit r1 c1 >==> LoopInit r2 c2)
         (LoopInit (s:=s1*s2)
                   (r1, r2)
                   ((Comb (i:=_*(_*_))
                          (fun '(i,(s1,s2)) =>
                             ret (i, s1, s2)))
                      >==> First c1
                      >==> (Comb (i:=_*_*_)
                                 (fun '(o1,s1',s2) =>
                                    ret (o1, s2, s1')))
                      >==> First c2
                      >==> (Comb (i:=_*_*_)
                                 (fun '(o2,s2',s1') =>
                                    ret (o2, (s1', s2')))))).
Proof.
  exists (fun s1 s2 =>
       s2 = (tt, (tt, fst (snd (fst s1)), tt, fst (snd (snd s1)),
                  tt, (snd (snd (fst s1)), snd (snd (snd s1)))))).
  cbn [circuit_state reset_state LoopInit value].
  split; [ reflexivity | ].
  intros; destruct_products; cbn [fst snd] in *; subst.
  simpl_ident. logical_simplify.
  cbn [step LoopInit fst snd]. simpl_ident.
  repeat (destruct_pair_let; cbn [fst snd]).
  ssplit; reflexivity.
Qed.

Lemma First_LoopInit {i o s t} r
      (c : Circuit (i * s) (o * s)) :
  cequiv (First (t:=t) (LoopInit r c))
         (LoopInit r
                   ((Comb (i:=_*_*_)
                          (fun '(i,t,s) => ret (i,s,t)))
                      >==> First c
                      >==> (Comb (i:=_*_*_)
                                 (fun '(o,s,t) => ret (o,t,s))))).
Proof.
  exists (fun s1 s2 =>
       s2 = (tt, (tt, fst (snd s1), tt, snd (snd s1)))).
  cbn [circuit_state reset_state LoopInit value].
  split; [ reflexivity | ].
  intros; destruct_products; cbn [fst snd] in *; subst.
  simpl_ident. logical_simplify.
  cbn [step LoopInit fst snd]. simpl_ident.
  repeat (destruct_pair_let; cbn [fst snd]).
  ssplit; reflexivity.
Qed.

Lemma Second_LoopInit {i o s t} r
      (c : Circuit (i * s) (o * s)) :
  cequiv (Second (t:=t) (LoopInit r c))
         (LoopInit r
                   ((Comb (i:=_*_*_)
                          (fun '(t,i,s) => ret (t,(i,s))))
                      >==> Second c
                      >==> (Comb (i:=_*(_*_))
                                 (fun '(t,(o,s)) => ret (t,o,s))))).
Proof.
  exists (fun s1 s2 =>
       s2 = (tt, (tt, fst (snd s1), tt, snd (snd s1)))).
  cbn [circuit_state reset_state LoopInit value].
  split; [ reflexivity | ].
  intros; destruct_products; cbn [fst snd] in *; subst.
  simpl_ident. logical_simplify.
  cbn [step LoopInit fst snd]. simpl_ident.
  repeat (destruct_pair_let; cbn [fst snd]).
  ssplit; reflexivity.
Qed.

Lemma LoopInit_LoopInit {i o s1 s2} r1 r2
      (c : Circuit (i * s1 * s2) (o * s1 * s2)) :
  cequiv (LoopInit r1 (LoopInit r2 c))
         (LoopInit (s:=s1*s2)
                   (r1, r2)
                   ((Comb (i:=_*(_*_))
                          (fun '(i,(s1,s2)) =>
                             ret (i, s1, s2)))
                      >==> c
                      >==> (Comb (i:=_*_*_)
                                 (fun '(o,s1,s2) =>
                                    ret (o, (s1, s2)))))).
Proof.
  exists (fun s1 s2 =>
       s2 = (tt, (tt, fst (snd (fst (snd s1))), tt,
                  (snd (snd s1), snd (snd (fst (snd s1))))))).
  cbn [circuit_state reset_state LoopInit value].
  split; [ reflexivity | ].
  intros; destruct_products; cbn [fst snd] in *; subst.
  simpl_ident. logical_simplify.
  cbn [step LoopInit fst snd]. simpl_ident.
  repeat (destruct_pair_let; cbn [fst snd]).
  ssplit; reflexivity.
Qed.

Lemma LoopInitCE_LoopInit {i o s1 s2} r1 r2 (c : Circuit (i * s1 * s2) (o * s1 * s2)) :
  cequiv (LoopInitCE r1 (LoopInit r2 c))
         (LoopInit (s:=s2*s1)
                   (r2, r1)
                   ((Comb (i:=_*_*(_*_))
                          (fun '(x, en, (s2, s1)) =>
                             ret (en, s1, (x, s1, s2)))
                          >==> Second c
                          >==> (Comb (i:=Bit*s1*(o*s1*s2))
                                     (o:=o*(s2*s1))
                                     (fun '(en, s1, (y, s1', s2')) =>
                                        s <- mux2 en (s1, s1') ;;
                                        ret (y, (s2', s))))))).
Proof.
  exists (fun s1 s2 =>
       s2 = (tt, (tt, fst (snd (fst s1)), tt,
                  (snd (snd (fst s1)), snd s1)))).
  cbn [circuit_state reset_state LoopInit value].
  split; [ reflexivity | ].
  intros; destruct_products; cbn [fst snd] in *; subst.
  simpl_ident. logical_simplify.
  cbn [step LoopInit fst snd]. simpl_ident.
  repeat (destruct_pair_let; cbn [fst snd]).
  simpl_ident. ssplit; reflexivity.
Qed.

Lemma extract_loops {i o} (c : Circuit i o) :
  cequiv c (LoopInit (loops_reset_state c) (loopless c)).
Proof.
  induction c; cbn [loopless].
  { rewrite LoopInit_ignore_state. reflexivity. }
  { rewrite IHc1 at 1. rewrite IHc2 at 1.
    apply LoopInit_merge. }
  { rewrite IHc at 1. apply First_LoopInit. }
  { rewrite IHc at 1. apply Second_LoopInit. }
  { simpl_ident. rewrite IHc at 1.
    apply LoopInitCE_LoopInit. }
  { rewrite LoopInit_ignore_state. reflexivity. }
Qed.

Fixpoint is_loop_free {i o} (c : Circuit i o) : bool :=
  match c with
  | Comb _ => true
  | Compose f g => (is_loop_free f && is_loop_free g)%bool
  | First f => is_loop_free f
  | Second f => is_loop_free f
  | DelayInitCE _ => true
  | LoopInitCE _ _ => false
  end.

Lemma move_delays {i o} (iresets : value i) (oresets : value o) (c : Circuit i o) :
  is_loop_free c = true ->
  oresets = snd (step c (reset_state c) iresets) ->
  cequiv (delays iresets >==> c) (c >==> delays oresets).
Admitted.

Lemma delay_input {i o} n m (c1 c2 : Circuit i o) resets :
  phase_retimed n m c1 (delays resets >==> c2) ->
  phase_retimed n (S m) c1 c2.
Admitted.

Lemma ndelay_state {i o} n m (c1 c2 : Circuit i o) resets :
  phase_retimed n m c1 (delays resets >==> c2) ->
  phase_retimed n m c1 c2.
Admitted.

Lemma phase_retimed_cequiv_iff {i o} (c1 c2 : Circuit i o) :
  phase_retimed 0 0 c1 c2 <-> cequiv c1 c2.
Proof.
  cbv [phase_retimed]. split; intros; logical_simplify.
  { destruct_lists_by_length. cbn [ndelays] in *.
    cbv [Par] in *. autorewrite with circuitsimpl in *.
    rewrite <-(extract_loops c2) in *. assumption. }
  { exists [], []. ssplit; [ reflexivity .. | ].
    cbn [ndelays]. cbv [Par]. autorewrite with circuitsimpl.
    rewrite <-extract_loops. assumption. }
Qed.

Axiom reassemble_state :
  forall {i o} (c : Circuit i o), value (circuit_state (loopless c)) -> value (loops_state c) -> value (circuit_state c).

Axiom loops_state_from_circuit_state :
  forall {i o} (c : Circuit i o), value (circuit_state c) -> value (loops_state c).

Global Instance Proper_phase_retimed {i o} :
  Proper (eq ==> eq ==> cequiv ==> cequiv ==> iff) (@phase_retimed i o).
Proof.
  repeat intro. subst.
  split; cbv [phase_retimed]; intros; logical_simplify.
  { lazymatch goal with
    | Heq : cequiv ?c1 ?c2, H : context [loopless ?c1] |- context [loopless ?c2] =>
      destruct Heq as [R [Hstart Hpres]]
    end.
    do 2 eexists; ssplit.
    3:{
      rewrite <-H1. rewrite H3.
      exists (fun (s1 : unit * (value (circuit_state (ndelays _))
                         * value (circuit_state (ndelays _))
                         * value (circuit_state (loopless _))
                         * value (loops_state _)))
           (s2 : unit * (value (circuit_state (ndelays _))
                         * value (circuit_state (ndelays _))
                         * value (circuit_state (loopless _))
                         * value (loops_state _))) =>
           R (reassemble_state _ (snd (fst (snd s1))) (snd (snd s1)))
             (reassemble_state _ (snd (fst (snd s2))) (snd (snd s2)))
           /\ ndelays_get (fst (fst (fst (snd s1)))) = ndelays_get (fst (fst (fst (snd s2))))
           /\ (Forall2
                (fun v1 v2 =>
                   exists u1 u2, R (reassemble_state _ u1 v1) (reassemble_state _ u2 v2))
                (ndelays_get (snd (fst (fst (snd s1)))))
                (ndelays_get (snd (fst (fst (snd s2))))))).
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
  eapply delay_input with (resets:=defaultValue).
  (* move the delay to the end of the circuit *)
  erewrite move_delays with (oresets:=true : value Bit) by reflexivity.
  (* insert another delay *)
  eapply delay_input with (resets:=defaultValue).
  (* move the delay in between the and2 and inv *)
  rewrite !Compose_assoc.
  erewrite move_delays with (oresets:=false : value Bit) by reflexivity.
  (* reflexivity *)
  apply phase_retimed_cequiv_iff.
  subst pipelined_nand; reflexivity.
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
             n 0
             (retimed_cipher_middle_round
                state key retimed_sbytes shrows mxcols add_rk)
             (cipher_middle_round sbytes shrows mxcols add_rk))
       As retimed_cipher_middle_round_correct.
Proof.
  intros. cbv [cipher_middle_round].
  autorewrite with circuitsimpl.
  cbv [phase_retimed] in * |- . logical_simplify.
  destruct_lists_by_length. cbn [ndelays] in *.
  cbv [Par] in *; autorewrite with circuitsimpl in *.
  


  
  (* insert a delay *)
  eapply delay_input with (resets:=defaultValue).
  (* move the delay to the end of the circuit *)
  erewrite move_delays with (oresets:=true : value Bit) by reflexivity.
  (* insert another delay *)
  eapply delay_input with (resets:=defaultValue).
  (* move the delay in between the and2 and inv *)
  rewrite !Compose_assoc.
  erewrite move_delays with (oresets:=false : value Bit) by reflexivity.
  (* reflexivity *)
  apply phase_retimed_cequiv_iff.
  subst pipelined_nand; reflexivity.
Qed.
Print pipelined_nand.
Check pipelined_nand_correct.
