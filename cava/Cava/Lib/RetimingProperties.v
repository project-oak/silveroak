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

Lemma move_delay {i o} (c : Circuit i o) r :
  is_loop_free c = true ->
  cequiv (DelayInit r >==> c) (c >==> DelayInit (snd (step c (reset_state c) r))).
Proof.
  revert r; induction c; intros.
  { (* Comb case *)
    exists (fun s1 s2 => snd s2 = c (fst s1)).
    cbn [value circuit_state reset_state step fst snd].
    ssplit; [ reflexivity | ].
    intros. destruct_products. cbn [fst snd] in *.
    ssplit; congruence. }
  { (* Compose case *)
    cbn [is_loop_free] in *.
    lazymatch goal with H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H end.
    logical_simplify. autorewrite with circuitsimpl.
    rewrite IHc1 by auto. rewrite <-(Compose_assoc _ _ c2).
    rewrite IHc2 by auto. autorewrite with circuitsimpl.
    cbn [step reset_state fst snd]. reflexivity. }
  { (* First case *)
    cbn [is_loop_free value] in *. destruct_products.
    cbn [reset_state fst snd step]. rewrite !split_delay.
    cbv [Par]. rewrite First_Second_comm.
    rewrite <-(Compose_assoc _ _ (First c)), <-First_Compose.
    rewrite IHc by auto.
    autorewrite with circuitsimpl; reflexivity. }
  { (* Second case *)
    cbn [is_loop_free value] in *. destruct_products.
    cbn [reset_state fst snd step]. rewrite !split_delay.
    cbv [Par]. autorewrite with circuitsimpl.
    rewrite <-(Compose_assoc _ _ (Second c)). rewrite <-Second_Compose.
    rewrite IHc by auto.
    autorewrite with circuitsimpl; reflexivity. }
  { (* LoopInitCE case *)
    cbn [is_loop_free] in *. discriminate. }
  { (* DelayInit case *)
    cbn [reset_state step fst snd].



                 
  intros.
  exists (fun s1 s2 =>
       step c (snd s1) (get_delays (fst s1)) = (fst s2, get_delays (snd s2))).
  cbn [value circuit_state reset_state fst snd]. ssplit.
  { rewrite !reset_delays.
    eexists.
    Unshelve. 2:cbn.

    2:exact (fun s1 s2 =>
         step c (snd s1) (get_delays (fst s1)) = (fst s2, get_delays (snd s2))).
    
  revert r; induction c; intros.
  { cbn [reset_state step fst snd].
    eexists.
    Unshelve. 2:cbn.
    exists (fun s1 s2 => s1 = 


  
  intros. cbv [cequiv].
  cbn [circuit_state value delays reset_state].
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

Lemma Par_Id_l_w {i o t} (f : Circuit i o) : wequiv (Par f (Id (t:=t))) (First f).
Proof. cbv [Par]. autorewrite with circuitsimplw. reflexivity. Qed.
Hint Rewrite @Par_Id_l_w using solve [eauto] : circuitsimplw.

Lemma Par_Id_r_w {i o t} (f : Circuit i o) : wequiv (Par (Id (t:=t)) f) (Second f).
Proof. cbv [Par]. autorewrite with circuitsimplw. reflexivity. Qed.
Hint Rewrite @Par_Id_r_w using solve [eauto] : circuitsimplw.

Lemma Second_Comb_w {i o t} f :
  wequiv (Second (Comb f)) (Comb (i:=t*i) (o:=t*o) (fun x => (fst x, f (snd x)))).
Proof.
  cbv [wequiv]. cbn. ssplit; intros; [ reflexivity | ].
  exists (fun i _ _ => i = 0); ssplit; intros; cbn [step fst snd]; try tauto; lia.
Qed.
Hint Rewrite @Second_Comb_w using solve [eauto] : pull_comb.

Lemma First_Comb_w {i o t} f :
  wequiv (First (Comb f)) (Comb (i:=i*t) (o:=o*t) (fun x => (f (fst x), snd x))).
Proof.
  cbv [wequiv]. cbn. ssplit; intros; [ reflexivity | ].
  exists (fun i _ _ => i = 0); ssplit; intros; cbn [step fst snd]; try tauto; lia.
Qed.
Hint Rewrite @First_Comb_w using solve [eauto] : pull_comb.

Lemma Compose_Comb_w {i t o} f g :
  wequiv (@Compose _ _ i t o (Comb f) (Comb g)) (Comb (f >=> g)).
Proof.
  cbv [wequiv]. cbn. ssplit; intros; [ reflexivity | ].
  exists (fun i _ _ => i = 0); ssplit; intros; cbn [step fst snd]; try tauto; lia.
Qed.
Hint Rewrite @Compose_Comb_w using solve [eauto] : pull_comb.

Lemma Compose_Comb_r_w {i t1 t2 o} c f g :
  wequiv (@Compose _ _ i t2 o (@Compose _ _ i t1 t2 c (Comb f)) (Comb g))
         (c >==> Comb (f >=> g)).
Proof.
  rewrite <-Compose_Comb_w. autorewrite with circuitsimplw. reflexivity.
Qed.
Hint Rewrite @Compose_Comb_r_w using solve [eauto] : pull_comb.

Lemma First_Second_comm {i1 i2 o1 o2} (c1 : Circuit i1 o1) (c2 : Circuit i2 o2) :
  wequiv (First c1 >==> Second c2) (Second c2 >==> First c1).
Admitted.

Lemma delays_Comb_comm {i o} (f : value i -> cava (value o)) :
  wequiv (delays >==> Comb f) (Comb f >==> delays).
Proof.
  Print wequiv.
  Search cequivn.
  induction i.
  induction n; cbn [ndelays]; autorewrite with circuitsimplw; [ reflexivity | ].
  rewrite <-(Compose_assoc_w _ _ _ _ (ndelays _) delays).
Qed.

Lemma ndelays_Comb_comm {i o} (f : value i -> cava (value o)) n :
  wequiv (ndelays n >==> Comb f) (Comb f >==> ndelays n).
Proof.
  induction n; cbn [ndelays]; autorewrite with circuitsimplw; [ reflexivity | ].
  rewrite <-(Compose_assoc_w _ _ _ _ (ndelays _) delays).
Qed.

Lemma Comb_ext {i o} (f g : value i -> cava (value o)) :
  (forall x, f x = g x) -> wequiv (Comb f) (Comb g).
Proof.
  intro Hext. cbv [wequiv]. cbn. ssplit; intros; [ reflexivity | ].
  exists (fun i _ _ => i = 0); ssplit; intros; cbn [step fst snd]; auto; lia.
Qed.

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
  Print phase_retimed.

  (* TODO: not quite working right now, how to properly incorporate retimed
     subcomponents? *)
Abort.
