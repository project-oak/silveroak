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

Lemma split_delay_init {t1 t2} (r1 : value t1) (r2 : value t2) :
  cequiv (DelayInit (t:=t1*t2) (r1, r2)) (Par (DelayInit r1) (DelayInit r2)).
Proof.
  exists eq. ssplit; [ reflexivity | ].
  cbn [value circuit_state Par].
  intros; subst; destruct_products. ssplit; reflexivity.
Qed.
Lemma split_delay {t1 t2} : cequiv (Delay (t:=t1*t2)) (Par Delay Delay).
Proof. apply split_delay_init. Qed.

Lemma LoopInitCE_Compose_l {i o s t}
      (c : Circuit t i) (body : Circuit (i * s) (o * s)) r :
  cequiv (First c >==> LoopInitCE r body)
         (LoopInitCE r (First c >==> body)).
Admitted.

Lemma LoopInit_Compose_l {i o s t}
      (c : Circuit t i) (body : Circuit (i * s) (o * s)) r :
  cequiv (c >==> LoopInit r body) (LoopInit r (First c >==> body)).
Admitted.

Lemma move_delay_init {i o} (c : Circuit i o) r :
  cequiv (DelayInit r >==> c)
         (chreset c (fst (step c (reset_state c) r))
                  >==> DelayInit (snd (step c (reset_state c) r))).
Proof.
  exists (fun (s1 : value i * value (circuit_state c))
       (s2 : value (circuit_state (chreset c _)) * value o) =>
       step c (snd s1) (fst s1) = (from_chreset_state (fst s2), snd s2)).
  cbn [fst snd reset_state from_chreset_state reset_state chreset
           circuit_state value].
  rewrite chreset_reset, from_to_chreset_state.
  rewrite <-surjective_pairing.
  ssplit; [ reflexivity | ].
  intros; destruct_products. cbn [step fst snd] in *.
  lazymatch goal with H : step _ _ _ = _ |- _ => rewrite H end.
  ssplit; [ reflexivity | ]. cbn [fst snd].
  rewrite step_chreset; cbn [fst snd].
  rewrite from_to_chreset_state.
  rewrite <-surjective_pairing.
  reflexivity.
Qed.

Lemma split_ndelays {t1 t2} n :
  cequiv (ndelays (t1*t2) n) (Par (ndelays t1 n) (ndelays t2 n)).
Proof.
  induction n; cbn [ndelays]; autorewrite with circuitsimpl; [ reflexivity | ].
  rewrite split_delay, IHn. cbv [Par]. autorewrite with circuitsimpl.
  eapply Proper_Compose; [ | reflexivity ].
  rewrite <-(Compose_assoc (First _) (Second _) (First _)).
  rewrite <-!First_Second_comm. autorewrite with circuitsimpl.
  reflexivity.
Qed.

(*
Fixpoint get_ndelays {t r} : value (circuit_state (ndelays (t:=t) r)) -> list (value t) :=
  match r with
  | [] => fun _ => []
  | _ :: _ => fun x => snd x :: get_ndelays (fst x)
  end.

Lemma reset_ndelays {t} r : get_ndelays (reset_state (ndelays (t:=t) r)) = r.
Proof.
  induction r; [ reflexivity .. | ].
  cbn [get_ndelays reset_state ndelays fst snd].
  rewrite IHr; reflexivity.
Qed.

Lemma step_ndelays2 {t} r s i :
  snd (step (ndelays (t:=t) r) s i) = hd i (get_ndelays s).
Proof.
  induction r; [ reflexivity | ].
  cbn [ndelays circuit_state value] in *; destruct_products.
  reflexivity.
Qed.

Lemma step_ndelays1 {t} r s i :
  get_ndelays (fst (step (ndelays (t:=t) r) s i)) = tl (get_ndelays s ++ [i]).
Proof.
  induction r; [ reflexivity .. | ].
  cbn [ndelays circuit_state value] in *; destruct_products.
  cbn [get_ndelays ndelays fst snd step app tl].
  rewrite IHr, step_ndelays2.
  destruct (get_ndelays _); reflexivity.
Qed.

Lemma split_delay {t1 t2} (r1 : value t1) (r2 : value t2) :
  cequiv (DelayInit (t:=t1*t2) (r1, r2)) (Par (DelayInit r1) (DelayInit r2)).
Proof.
  exists eq. ssplit; [ reflexivity | ]. cbn [value circuit_state Par].
  intros; subst; destruct_products. ssplit; reflexivity.
Qed.

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
 *)

Lemma Par_Id_l {i o t} (f : Circuit i o) : cequiv (Par f (Id (t:=t))) (First f).
Proof. cbv [Par]. autorewrite with circuitsimpl. reflexivity. Qed.
Hint Rewrite @Par_Id_l using solve [eauto] : circuitsimpl.

Lemma Par_Id_r {i o t} (f : Circuit i o) : cequiv (Par (Id (t:=t)) f) (Second f).
Proof. cbv [Par]. autorewrite with circuitsimpl. reflexivity. Qed.
Hint Rewrite @Par_Id_r using solve [eauto] : circuitsimpl.

Lemma Second_Comb {i o t} f :
  cequiv (Second (Comb f)) (Comb (i:=t*i) (o:=t*o) (fun x => (fst x, f (snd x)))).
Proof.
  exists (fun _ _ => True). cbn [value circuit_state]. ssplit; [ tauto | ].
  intros; logical_simplify. cbn [step fst snd]. ssplit; tauto.
Qed.
Hint Rewrite @Second_Comb using solve [eauto] : pull_comb.

Lemma First_Comb {i o t} f :
  cequiv (First (Comb f)) (Comb (i:=i*t) (o:=o*t) (fun x => (f (fst x), snd x))).
Proof.
  exists (fun _ _ => True). cbn [value circuit_state]. ssplit; [ tauto | ].
  intros; logical_simplify. cbn [step fst snd]. ssplit; tauto.
Qed.
Hint Rewrite @First_Comb using solve [eauto] : pull_comb.

Lemma Compose_Comb {i t o} f g :
  cequiv (@Compose _ _ i t o (Comb f) (Comb g)) (Comb (f >=> g)).
Proof.
  exists (fun _ _ => True). cbn [value circuit_state]. ssplit; [ tauto | ].
  intros; logical_simplify. cbn [step fst snd]. ssplit; tauto.
Qed.
Hint Rewrite @Compose_Comb using solve [eauto] : pull_comb.

Lemma Compose_Comb_r {i t1 t2 o} c f g :
  cequiv (@Compose _ _ i t2 o (@Compose _ _ i t1 t2 c (Comb f)) (Comb g))
         (c >==> Comb (f >=> g)).
Proof.
  rewrite <-Compose_Comb. autorewrite with circuitsimpl. reflexivity.
Qed.
Hint Rewrite @Compose_Comb_r using solve [eauto] : pull_comb.

Lemma loopless_loop_free {i o} (c : Circuit i o) :
  is_loop_free c = true -> cequiv (loopless c) (First c).
Proof.
  induction c; cbn [loopless is_loop_free];
    rewrite ?Bool.andb_true_iff; intros; logical_simplify.
  { (* Comb *)
    reflexivity. }
  { (* Compose *)
    rewrite IHc1, IHc2 by auto.
    exists (fun (s1 : unit * value (circuit_state c1) * unit * value (circuit_state c2) * unit)
         (s2 : value (circuit_state c1) * value (circuit_state c2)) =>
         s1 = (tt, fst s2, tt, snd s2, tt)).
    cbn [value circuit_state reset_state loops_state fst snd].
    ssplit; [ reflexivity | ].
    intros; subst; destruct_products; cbn [fst snd step].
    ssplit; reflexivity. }
  { (* First *)
    rewrite IHc by auto.
    exists (fun (s1 : unit * value (circuit_state c) * unit) (s2: value (circuit_state c)) =>
         s1 = (tt, s2, tt)).
    cbn [value circuit_state reset_state loops_state fst snd].
    ssplit; [ reflexivity | ].
    intros; subst; destruct_products; cbn [fst snd step].
    ssplit; reflexivity. }
  { (* Second *)
    rewrite IHc by auto.
    exists (fun (s1 : unit * value (circuit_state c) * unit) (s2: value (circuit_state c)) =>
         s1 = (tt, s2, tt)).
    cbn [value circuit_state reset_state loops_state fst snd].
    ssplit; [ reflexivity | ].
    intros; subst; destruct_products; cbn [fst snd step].
    ssplit; reflexivity. }
  { (* Loop *)
    discriminate. }
  { (* Delay *)
    reflexivity. }
Qed.

About to_chreset_state.

Axiom reassemble_state :
  forall {i o} (c : Circuit i o), value (circuit_state (loopless c)) -> value (loops_state c) -> value (circuit_state c).

Axiom loops_state_from_circuit_state :
  forall {i o} (c : Circuit i o), value (circuit_state c) -> value (loops_state c).
Axiom loopless_state_from_circuit_state :
  forall {i o} (c : Circuit i o), value (circuit_state c) -> value (circuit_state (loopless c)).

Axiom to_chreset_loops_state :
  forall {i o} {c : Circuit i o} {r : value (circuit_state c)}, value (loops_state c) -> value (loops_state (chreset c r)).
Axiom from_chreset_loops_state :
  forall {i o} {c : Circuit i o} {r : value (circuit_state c)}, value (loops_state (chreset c r)) -> value (loops_state c).

Eval simpl in (fun r c => loops_state (DelayInit r >==> c)).
Locate swap.
Eval simpl in
    (fun i o r c =>
       Circuit (i * loops_state (DelayInit r >==> c)) (o * loops_state (DelayInit r >==> c))).
Eval simpl in (fun i o r c =>
 Circuit (i * loops_state (chreset c (fst (step c (reset_state c) r)) >==> DelayInit (snd (step c (reset_state c) r))))
         (o * loops_state (chreset c (fst (step c (reset_state c) r)) >==> DelayInit (snd (step c (reset_state c) r))))).

Lemma move_delay_loopless {i o} (c : Circuit i o) r :
  cequiv (loopless (DelayInit r >==> c))
         (Second (Comb (i:=(tzero*loops_state c))
                       (o:=(loops_state (chreset c _)*tzero))
                       (fun x => (to_chreset_loops_state (snd x), tt)))
            >==> (loopless
                    (chreset c (fst (step c (reset_state c) r))
                             >==> DelayInit (snd (step c (reset_state c) r))))
            >==> Second (Comb (i:=(loops_state (chreset c _)*tzero))
                              (o:=(tzero * loops_state c))
                              (fun x => (tt, from_chreset_loops_state (fst x))))).
Admitted.
(*
(* i, (s1, s2)

   == First c1 >==> Second (Comb (fun s => snd s)) >==> loopless c2
*)
Lemma loopless_Compose_loop_free_l {i o t} (c1 : Circuit i t) (c2 : Circuit t o) :
  is_loop_free c1 = true ->
  cequiv (loopless (c1 >==> c2))
         ((First c1)
            >==> (Comb (i:=t*(loops_state c1*loops_state c2)) (o:=_*_*_) (fun '(t,s1,s2) => (t,s2,s1)
            (fun 
         ) >==> loopless c2).
 (Second c1 >==> loopless c2).
  
  loopless (Delay >==> c2)
*)
Lemma loopless_chreset {i o} (c : Circuit i o) r :
  cequiv (loopless (chreset c r))
         (Second (Comb from_chreset_loops_state)
                 >==> chreset (loopless c) (loopless_state_from_circuit_state c r)
                 >==> Second (Comb to_chreset_loops_state)).
Admitted.

Lemma ndelays_succ_l {t} n : cequiv (ndelays t (S n)) (Delay >==> ndelays t n).
Proof.
  induction n; cbn [ndelays]; autorewrite with circuitsimpl; [ reflexivity | ].
  rewrite <-IHn. reflexivity.
Qed.

Fixpoint Forall_ndelays {t1 t2 n} (R : value t1 -> value t2 -> Prop)
  : value (circuit_state (ndelays t1 n))
    -> value (circuit_state (ndelays t2 n)) -> Prop :=
  match n with
  | 0 => fun _ _ => True
  | S _ =>
    fun d1 d2 =>
      Forall_ndelays R (fst d1) (fst d2) /\ R (snd d1) (snd d2)
  end.

Lemma reassemble_reset_state {i o} (c : Circuit i o) :
  reassemble_state c (reset_state (loopless c)) (loops_reset_state c) = reset_state c.
Admitted.

(* TODO: this should be cequiv ==> cequiv ==> iff *)
Instance Proper_retimed {i o} n m :
  Proper (cequiv ==> eq ==> iff) (@retimed i o n m).
Proof.
  intros a b Hab c d Hcd. subst. cbv [retimed].
  split.
  { intros [r Hac]; logical_simplify.
    exists r. rewrite <-Hab, Hac. reflexivity. }
  { intros [r Hbd]; logical_simplify.
    exists r. rewrite Hab, Hbd. reflexivity. }
Qed.

Lemma retimed_trans {i o} n m n' m' (c1 c2 c3 : Circuit i o) :
  retimed n m c1 c2 -> retimed n' m' c2 c3 ->
  retimed (n + n') (m + m') c1 c3.
Admitted.

Lemma delay1_output {i o} n m (c1 c2 : Circuit i o) :
  retimed n m c1 (c2 >==> Delay) ->
  retimed (S n) m c1 c2.
Proof.
  intros.
  replace (S n) with (n + 1) by lia. replace m with (m + 0) by lia.
  eapply retimed_trans; [ eassumption | ].
  cbv [retimed]. cbn [Par circuit_state chreset value ndelays Id].
  exists (tt, defaultValue, tt). cbn [fst snd].
  autorewrite with circuitsimpl.
  change defaultValue with (reset_state (Delay (t:=o))).
  rewrite chreset_noop, LoopInit_First_r.
  rewrite <-extract_loops. reflexivity.
Qed.

Lemma delay1_input {i o} n m (c1 c2 : Circuit i o) :
  retimed n m c1 (Delay >==> c2) ->
  retimed (S n) m c1 (chreset c2 (fst (step c2 (reset_state c2) defaultValue))).
Proof.
  intros.
  replace (S n) with (n + 1) by lia.
  replace m with (m + 0) by lia.
  eapply retimed_trans; [ eassumption | ].
  cbv [Delay]. rewrite move_delay_init.
  cbv [retimed]. cbn [Par circuit_state chreset value ndelays Id Delay].
  exists (tt, snd (step c2 (reset_state c2) defaultValue), tt). cbn [fst snd].
  autorewrite with circuitsimpl.
  rewrite LoopInit_First_r. rewrite <-extract_loops.
  reflexivity.
Qed.

Require Import Coq.derive.Derive.

Local Ltac simpl_resets :=
  cbn [step fst snd defaultValue default_value
            CombinationalSemantics defaultSignal defaultCombValue].

Derive pipelined_nand
       SuchThat (retimed
                   2 0 pipelined_nand
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
  Print phase_retimed.

  (* TODO: not quite working right now, how to properly incorporate retimed
     subcomponents? *)
Abort.

Lemma loopless_LoopInit {i o s} (body : Circuit (i * s) (o * s)) r :
  wequiv (loopless (LoopInit r body))
         (Comb (i:=(_*(_*(_*_)))) (o:=_*_*_)
               (fun '(x, (_, (body_st, loop_st))) => (x, loop_st, body_st))
               >==> loopless body
               >==> (Comb (i:=_*_*_) (o:=(_*(tzero*(_*_))))
                          (fun '(x, loop_st, body_st) => (x, (tt, (body_st, loop_st)))))).
Proof.
  cbv [wequiv]. ssplit; intros; [ cbn; lia | ].
  cbn [cpath loopless LoopInit]. autorewrite with natsimpl. simpl_ident.
  cbv [cequivn]. cbn [value loops_state LoopInit circuit_state].
  destruct (cequivn_reflexive (loopless body) ltac:(apply is_loop_free_loopless))
    as [Rb ?]. logical_simplify.
  exists (fun i s1 s2 => Rb i (snd (fst (snd (fst s1)))) (snd (fst s2))).
  ssplit.
  { intros; destruct_products. cbn. auto. }
  { intros; destruct_products. cbn.
    repeat lazymatch goal with x : unit |- _ => destruct x end.
    repeat destruct_pair_let. cbn [fst snd].
    lazymatch goal with H : cpath _ = 0 -> _ |- _ => erewrite H by auto end.
    reflexivity. }
  { intros; destruct_products; cbn.
    repeat lazymatch goal with x : unit |- _ => destruct x end.
    repeat destruct_pair_let. cbn [fst snd] in *.
    lazymatch goal with H : forall _ _ _ _, Rb 1 _ _ -> _ |- _ =>
                        erewrite H by eauto end.
    reflexivity. }
  { intros; destruct_products; cbn.
    repeat lazymatch goal with x : unit |- _ => destruct x end.
    repeat destruct_pair_let. cbn [fst snd] in *. eauto. }
Qed.

Lemma retime_loop {i o s} (f g : Circuit (i * s) (o * s)) n r :
  phase_retimed n n f g ->
  phase_retimed n n (LoopInit r f) (LoopInit r g).
Proof.
  cbv [phase_retimed]. intros [proj_gf [proj_fg [Hproj Hequiv]]].
  cbn [loops_state value LoopInit].
  exists (fun x => (fst x, (proj_gf (fst (snd x)), snd (snd x)))).
  exists (fun x => (fst x, (proj_fg (fst (snd x)), snd (snd x)))).
  rewrite !loopless_LoopInit. rewrite Hequiv.
  split; [ intros; destruct_products; cbn [fst snd]; rewrite Hproj;
           reflexivity | ].
  autorewrite with circuitsimplw pull_comb.
  cbv [mcompose]; simpl_ident.
  (* RHS has delays and Comb flipped around *)
  repeat eapply Proper_Compose.
  (* need Proper_comb with funext *)
  (* each subcircuit should now be equiivalent *)
  eapply Proper_Comb.
  Print phase_retimed.
  (* objective: get to Second (Par (ndelays n) (ndelays n)) >==> loopless g) and rewrite *)
  
  Search LoopInitCE.
Qed.

Instance phase_retimed_0_refl {i o} : Reflexive (@phase_retimed i o 0 0) | 10.
Proof.
  intro c. cbv [phase_retimed]. exists id, id. split; [ reflexivity | ].
  change (Comb (semantics:=CombinationalSemantics) (@id (value (loops_state c))))
    with (Id (t:=loops_state c)).
  autorewrite with circuitsimplw. reflexivity.
Qed.

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
  Print phase_retimed.

  (* TODO: not quite working right now, how to properly incorporate retimed
     subcomponents? *)
Abort.
