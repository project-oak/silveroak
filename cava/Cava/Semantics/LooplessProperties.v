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

Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Loopless.
Require Import Cava.Util.Tactics.
Import Circuit.Notations.

Fixpoint is_loop_free {i o} (c : Circuit i o) : bool :=
  match c with
  | Comb _ => true
  | Compose f g => (is_loop_free f && is_loop_free g)%bool
  | Par f g => (is_loop_free f && is_loop_free g)%bool
  | DelayInit _ => true
  | LoopInitCE _ _ => false
  end.

Lemma is_loop_free_loopless {i o} (c : Circuit i o) :
  is_loop_free (loopless c) = true.
Proof.
  induction c; cbn [loopless is_loop_free First Second];
    boolsimpl; auto;
      repeat match goal with H : _ = true |- _ => rewrite H end;
      reflexivity.
Qed.

Lemma LoopInit_ignore_state {i o s} resetval (c : Circuit i o) :
  cequiv (LoopInit (s:=s) resetval (First c)) c.
Proof.
  exists (fun s1 s2 => fst (fst (snd s1)) = s2). cbn [circuit_state LoopInit value].
  split; [ reflexivity | ].
  intros; destruct_products; cbn [fst snd] in *; subst.
  cbn [step LoopInit First fst snd]. simpl_ident.
  split; reflexivity.
Qed.

Lemma LoopInit_merge {i1 o1 o2 s1 s2} r1 r2
      (c1 : Circuit (i1 * s1) (o1 * s1))
      (c2 : Circuit (o1 * s2) (o2 * s2)) :
  cequiv (LoopInit r1 c1 >==> LoopInit r2 c2)
         (LoopInit (s:=s1*s2)
                   (r1, r2)
                   ((Comb (i:=_*(_*_)) (o:=_*_*_)
                          (fun '(i,(s1,s2)) => (i, s1, s2)))
                      >==> First c1
                      >==> (Comb (i:=_*_*_) (o:=_*_*_)
                                 (fun '(o1,s1',s2) => (o1, s2, s1')))
                      >==> First c2
                      >==> (Comb (i:=_*_*_) (o:=_*(_*_))
                                 (fun '(o2,s2',s1') => (o2, (s1', s2')))))).
Proof.
  exists (fun s1 s2 =>
       s2 = (tt, (tt, (fst (snd (fst s1)), tt), tt,
             (fst (snd (snd s1)), tt), tt,
             (snd (snd (fst s1)), snd (snd (snd s1)))))).
  cbn [circuit_state reset_state LoopInit value fst snd First Id].
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
                   ((Comb (i:=_*_*_) (o:=_*_*_)
                          (fun '(i,t,s) => (i,s,t)))
                      >==> First c
                      >==> (Comb (i:=_*_*_) (o:=_*_*_)
                                 (fun '(o,s,t) => (o,t,s))))).
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
                   ((Comb (i:=_*_*_) (o:=_*(_*_))
                          (fun '(t,i,s) => (t,(i,s))))
                      >==> Second c
                      >==> (Comb (i:=_*(_*_)) (o:=_*_*_)
                                 (fun '(t,(o,s)) => (t,o,s))))).
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
                   ((Comb (i:=_*(_*_)) (o:=_*_*_)
                          (fun '(i,(s1,s2)) => (i, s1, s2)))
                      >==> c
                      >==> (Comb (i:=_*_*_) (o:=_*(_*_))
                                 (fun '(o,s1,s2) => (o, (s1, s2)))))).
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

Lemma LoopInitCE_LoopInit {i o s1 s2} r1 r2
      (c : Circuit (i * s1 * s2) (o * s1 * s2)) :
  cequiv (LoopInitCE r1 (LoopInit r2 c))
         (LoopInit (s:=s2*s1)
                   (r2, r1)
                   ((Comb (i:=_*_*(_*_)) (o:=_*_*(_*_*_))
                          (fun '(x, en, (s2, s1)) => (en, s1, (x, s1, s2)))
                          >==> Second c
                          >==> (Comb (i:=Bit*s1*(o*s1*s2))
                                     (o:=o*(s2*s1))
                                     (fun '(en, s1, (y, s1', s2')) =>
                                        (y, (s2', if (en : bool) then s1' else s1))))))).
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
