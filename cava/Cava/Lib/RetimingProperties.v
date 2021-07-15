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

Lemma move_delay {i o} (c : Circuit i o) :
  cequiv (Delay >==> c)
         (chreset c (fst (step c (reset_state c) defaultValue))
                  >==> DelayInit (snd (step c (reset_state c) defaultValue))).
Proof. apply move_delay_init. Qed.

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

Lemma ndelays_succ_l {t} n : cequiv (ndelays t (S n)) (Delay >==> ndelays t n).
Proof.
  induction n; cbn [ndelays]; autorewrite with circuitsimpl; [ reflexivity | ].
  rewrite <-IHn. reflexivity.
Qed.

Lemma simulate_retimed {i o} (c1 c2 : Circuit i o) n :
  retimed n c1 c2 ->
  forall input1 input2 : list (value i),
    (forall i, nth i input2 defaultValue = nth (i*(n+1)) input1 defaultValue) ->
    forall i,
      0 < i ->
      nth i (simulate c2 input2) defaultValue
      = nth (i*n) (simulate c1 input1) defaultValue.
Proof.
  intros [r Hr]. intros.
  erewrite (simulate_cequiv c1) by eauto.
  cbv [simulate].
  (* separate input1 into (length input2) lists of multiple inputs, prove that
     executing each list is equivalent to one execution of c2 *)
Admitted.

Fixpoint Forall_ndelays {t1 t2 n} (R : value t1 -> value t2 -> Prop)
  : value (circuit_state (ndelays t1 n))
    -> value (circuit_state (ndelays t2 n)) -> Prop :=
  match n with
  | 0 => fun _ _ => True
  | S _ =>
    fun d1 d2 =>
      Forall_ndelays R (fst d1) (fst d2) /\ R (snd d1) (snd d2)
  end.

(* TODO: the definition of cequiv might need to change to make this provable; in
   particular, the loop and non-loop states need to be able to vary
   independently *)
Instance Proper_retimed {i o} n :
  Proper (cequiv ==> cequiv ==> iff) (@retimed i o n).
Admitted.

Lemma retimed_trans {i o} n n' (c1 c2 c3 : Circuit i o) :
  retimed n c1 c2 -> retimed n' c2 c3 -> retimed (n + n') c1 c3.
Admitted.

Lemma LoopInit_ignore_input {t s} r (c : Circuit s s) :
  cequiv (LoopInit r (Second c)) (Id (t:=t)).
Proof.
  exists (fun _ _ => True). ssplit; [ tauto | ].
  cbn [LoopInit circuit_state value Id].
  intros; destruct_products; cbn [fst snd] in *. logical_simplify.
  cbn [step LoopInit Id fst snd]. ssplit; auto.
Qed.
Hint Rewrite @LoopInit_ignore_input using solve [eauto] : circuitsimpl.

Lemma retimed_delay_r {i o} (c : Circuit i o) :
  is_loop_free c = true -> retimed 1 (c >==> Delay) c.
Proof.
  cbv [retimed]. cbn [Par circuit_state chreset value ndelays Id Delay].
  exists (tt, (defaultValue, defaultValue)). cbn [fst snd].
  autorewrite with circuitsimpl. rewrite split_delay_init.
  rewrite loopless_loop_free by auto. cbv [Par].
  rewrite <-!LoopInit_Compose_l, LoopInit_ignore_input.
  autorewrite with circuitsimpl. reflexivity.
Qed.

Lemma delay1_output {i o} n (c1 c2 : Circuit i o) :
  is_loop_free c2 = true ->
  retimed n c1 (c2 >==> Delay) -> retimed (S n) c1 c2.
Proof.
  intros. replace (S n) with (n + 1) by lia.
  eapply retimed_trans; [ eassumption | ].
  eapply retimed_delay_r; auto.
Qed.

Lemma retimed_cequiv {i o} (c1 c2 : Circuit i o) :
  retimed 0 c1 c2 <-> cequiv c1 c2.
Proof.
  cbv [retimed]. cbn [ndelays Par circuit_state value chreset Id].
  split.
  { intros [? Heq]. rewrite Heq.
    autorewrite with circuitsimpl.
    rewrite <-extract_loops. reflexivity. }
  { intros Heq. eexists_destruct.
    autorewrite with circuitsimpl.
    rewrite <-extract_loops. auto. }
Qed.

Global Instance Reflexive_retimed {i o} : Reflexive (@retimed i o 0) | 10.
Proof. repeat intro. apply retimed_cequiv; reflexivity. Qed.

Lemma DelayInit_Comb_comm {i o} (f : value i -> cava (value o)) r :
  cequiv (DelayInit r >==> Comb f) (Comb f >==> DelayInit (f r)).
Proof.
  rewrite move_delay_init. cbn [chreset step fst snd].
  reflexivity.
Qed.

Fixpoint map_ndelays {t1 t2 n} (f : value t1 -> value t2)
  : @value combType (circuit_state (ndelays t1 n))
    -> @value combType (circuit_state (ndelays t2 n)) :=
  match n with
  | 0 => fun x => x
  | S _ => fun x => (map_ndelays f (fst x), f (snd x))
  end.

Lemma ndelays_Comb_comm {i o} (f : value i -> cava (value o)) n :
  cequiv (ndelays i n >==> Comb f)
         (Comb f >==> chreset (ndelays o n) (map_ndelays f defaultValue)).
Proof.
  induction n; cbn [ndelays]; autorewrite with circuitsimpl; [ reflexivity | ].
  cbv [Delay]. rewrite <-Compose_assoc. rewrite DelayInit_Comb_comm.
  cbn [chreset map_ndelays fst snd]. autorewrite with circuitsimpl.
  rewrite IHn. reflexivity.
Qed.

Lemma retimed_cancel_r {i o t} n (c1 c2 : Circuit i t) (c3 : Circuit t o) :
  retimed n c1 c2 -> retimed n (c1 >==> c3) (c2 >==> c3).
Admitted.

Lemma retimed_cancel_l {i o t} n (c1 c2 : Circuit t o) (c3 : Circuit i t) :
  retimed n c1 c2 -> retimed n (c3 >==> c1) (c3 >==> c2).
Admitted.

Lemma loopless_par {i1 i2 o1 o2} (c1 : Circuit i1 o1) (c2 : Circuit i2 o2) :
  cequiv (loopless (Par c1 c2))
         (Comb (i:=_*_*(_*_)) (o:=_*_*(_*_))
               (fun '(x1,x2,(s1,s2)) => (x1,s1,(x2,s2)))
               >==> Par (loopless c1) (loopless c2)
               >==> (Comb (i:=_*_*(_*_)) (o:=_*_*(_*_))
                          (fun '(x1,s1,(x2,s2)) => (x1,x2,(s1,s2))))).
Admitted.

(* LHS : x1,s1 / x2,s2*)
(* RHS : x1,x2,(s1,s2) *)
Lemma Par_LoopInit {i1 o1 s1 i2 o2 s2} (c1 : Circuit (i1 * s1) (o1 * s1))
      (c2 : Circuit (i2 * s2) (o2 * s2)) r1 r2 :
  cequiv (Par (LoopInit r1 c1) (LoopInit r2 c2))
         (LoopInit
            (s:=s1*s2) (r1,r2)
            (Comb (i:=_*_*(_*_)) (o:=_*_*(_*_))
                  (fun '(x1,x2,(s1,s2)) => (x1,s1,(x2,s2)))
                  >==> Par c1 c2
                  >==> (Comb (i:=_*_*(_*_)) (o:=_*_*(_*_))
                             (fun '(x1,s1,(x2,s2)) => (x1,x2,(s1,s2)))))).
Proof.
Admitted.

Lemma retimed_par {i1 i2 o1 o2}
      (c1 c2 : Circuit i1 o1) (c3 c4 : Circuit i2 o2) n :
  retimed n c1 c2 -> retimed n c3 c4 -> retimed n (Par c1 c3) (Par c2 c4).
Proof.
  cbv [retimed]. cbn [circuit_state Par value]. intros.
  logical_simplify. eexists.
  repeat match goal with H : cequiv _ _ |- _ => rewrite H end.
  rewrite loopless_par. rewrite Par_LoopInit.
  eapply Proper_LoopInit; [ reflexivity | ].
  (* need to be able to move the delays over Comb *)
Admitted.

Lemma loop_free_ndelays {t} n : is_loop_free (ndelays t n) = true.
Proof.
  induction n; [ reflexivity | ]. cbn [ndelays is_loop_free].
  rewrite IHn; reflexivity.
Qed.

Lemma retimed_ndelays {t} n : retimed n (ndelays t n) Id.
Proof.
  induction n; [ reflexivity | ]. cbn [ndelays].
  replace (S n) with (1 + n) by lia.
  eapply retimed_trans; [ | eassumption ].
  apply retimed_delay_r; apply loop_free_ndelays.
Qed.

Lemma retimed_first {i o t} (c1 c2 : Circuit i o) n :
  retimed n c1 c2 -> retimed n (Par c1 (ndelays t n)) (First c2).
Proof.
  intros. rewrite <-Par_Id_l.
  apply retimed_par; [ assumption | ].
  apply retimed_ndelays.
Qed.

Lemma retimed_second {i o t} (c1 c2 : Circuit i o) n :
  retimed n c1 c2 -> retimed n (Par (ndelays t n) c1) (Second c2).
Proof.
  intros. rewrite <-Par_Id_r.
  apply retimed_par; [ | assumption ].
  apply retimed_ndelays.
Qed.

Lemma retimed_LoopInit {i o s} (c1 c2 : Circuit (i * s) (o * s)) n r :
  retimed n c1 c2 -> retimed n (LoopInit r c1) (LoopInit r c2).
Proof.
  intros [v Hv]. rewrite Hv. clear Hv.
  rewrite LoopInit_LoopInit.
  autorewrite with circuitsimpl.
  cbv [retimed]. eexists.
  cbn [loops_reset_state LoopInit].
  exists (fun (s1 : unit * (unit * value (circuit_state (loopless c2))
                     * value (circuit_state (chreset (ndelays (o * s * loops_state c2) n) v))
                     * unit *  (value s * value (loops_state c2))))
       (s2 : unit * (unit * unit * unit
                     * (unit * value (circuit_state (loopless c2)) * unit)
                     * unit
                     * value (circuit_state (chreset (ndelays (o * (tzero * (loops_state c2 * s))) n) _))
                     * (unit * (value (loops_state c2) * value s)))) =>
       let '(_,(_,ll1,d1,_,(s1,ls1))) := s1 in
       let '(_,(_,_,_,(_,ll2,_),_,d2,(_,(ls2,s2)))) := s2 in
       ll1 = ll2
       /\ ls1 = ls2
       /\ s1 = s2
       /\ Forall_ndelays
           (t1:=o * s * loops_state c2)
           (t2:= o * (tzero * (loops_state c2 * s)))
           (fun (s1 : value o * value s * value (loops_state c2))
              (s2 : value o * (unit * (value (loops_state c2) * value s))) =>
              s2 = (fst (fst s1), (tt, (snd s1, snd (fst s1)))))
           (from_chreset_state d1) (from_chreset_state d2)).
  cbn [LoopInit reset_state circuit_state value loops_state loopless].
  ssplit; [ reflexivity .. | | ].
  (* Instantiate rvals with a mapping from v, then this works *)
Admitted.

Lemma retimed_Loop {i o s} (c1 c2 : Circuit (i * s) (o * s)) n :
  retimed n c1 c2 -> retimed n (Loop c1) (Loop c2).
Proof. apply retimed_LoopInit. Qed.

Require Import Coq.derive.Derive.
Require Import Cava.Lib.Combinators.
Require Import Cava.Lib.CombinatorsProperties.

Derive pipelined_nand
       SuchThat (retimed
                   2 pipelined_nand
                   (Comb (i:=Bit*Bit) (o:=Bit) and2
                         >==> Comb (o:=Bit) inv))
       As pipelined_nand_correct.
Proof.
  (* insert a delay at the end *)
  apply delay1_output; [ reflexivity | ].
  (* add the delay to the pipelined circuit *)
  apply retimed_cancel_r.
  (* add the inv to the pipelined circuit *)
  apply retimed_cancel_r.
  (* insert another delay *)
  apply delay1_output; [ reflexivity | ].
  (* done! *)
  reflexivity.
Qed.
Print pipelined_nand.
Check pipelined_nand_correct.


Section WithSubroutines.
  Context {state key : type}
          (sbytes : Circuit state state)
          (shrows : Circuit state state)
          (mxcols : Circuit state state)
          (add_rk : Circuit (state * key) state).

  Definition cipher_middle_round : Circuit (state * key) state :=
    First (sbytes >==> shrows >==> mxcols) >==> add_rk.

  Definition cipher : Circuit key state :=
    Loop (Comb (i:=_*_) (o:=_*_) swap
               >==> cipher_middle_round
               >==> Comb (o:=_*_) fork2).
End WithSubroutines.

Derive retimed_cipher_middle_round
       SuchThat
       (forall {state key} n
          (sbytes retimed_sbytes shrows mxcols : Circuit state state)
          (add_rk : Circuit (state * key) state),
           retimed n retimed_sbytes sbytes ->
           retimed
             n
             (retimed_cipher_middle_round
                state key n retimed_sbytes shrows mxcols add_rk)
             (cipher_middle_round sbytes shrows mxcols add_rk))
       As retimed_cipher_middle_round_correct.
Proof.
  intros. cbv [cipher_middle_round].
  autorewrite with circuitsimpl.
  apply retimed_cancel_r.
  apply retimed_cancel_r.
  apply retimed_cancel_r.
  apply retimed_first.
  eassumption.
Qed.
Print retimed_cipher_middle_round.
Check retimed_cipher_middle_round_correct.

Derive retimed_cipher
       SuchThat
       (forall {state key} n
          (sbytes retimed_sbytes shrows mxcols : Circuit state state)
          (add_rk : Circuit (state * key) state),
           retimed n retimed_sbytes sbytes ->
           retimed
             n
             (retimed_cipher
                state key n retimed_sbytes shrows mxcols add_rk)
             (cipher sbytes shrows mxcols add_rk))
       As retimed_cipher_correct.
Proof.
  intros. cbv [cipher].
  autorewrite with circuitsimpl.
  (* lift loop onto retimed circuit *)
  apply retimed_Loop.
  (* cancel out combinational components *)
  apply retimed_cancel_r.
  apply retimed_cancel_l.
  (*  use the retimed middle round lemma *)
  apply (retimed_cipher_middle_round_correct state).
  (* done! *)
  eassumption.
Qed.
Print retimed_cipher.
Check retimed_cipher_correct.
