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

Require Import Coq.Classes.Morphisms.
Require Import coqutil.Tactics.Tactics.
Require Import ExtLib.Structures.Monad.
Require Import Cava.Core.Core.
Require Import Cava.Semantics.Combinational.
Require Import Cava.Semantics.Equivalence.
Require Import Cava.Semantics.Loopless.
Require Import Cava.Semantics.LooplessProperties.
Require Import Cava.Semantics.WeakEquivalence.
Require Import Cava.Semantics.Simulation.
Require Import Cava.Lib.CircuitTransforms.
Require Import Cava.Util.List.
Require Import Cava.Util.Tactics.
Import MonadNotation Circuit.Notations.

Local Ltac simplify :=
  cbn [circuit_state step Id value]; intros;
  destruct_products; cbn [fst snd] in *;
  repeat (destruct_pair_let; cbn [fst snd]);
  logical_simplify; simpl_ident; subst.

Lemma First_Id {t1 t2} : @cequiv (t1 * t2) (t1 * t2) (First Id) Id.
Proof.
  exists eq. ssplit; [ reflexivity | ]. simplify. ssplit; reflexivity.
Qed.
Hint Rewrite @First_Id using solve [eauto] : circuitsimpl.

Lemma Second_Id {t1 t2} : @cequiv (t1 * t2) (t1 * t2) (Second Id) Id.
Proof.
  exists eq. ssplit; [ reflexivity | ]. simplify. ssplit; reflexivity.
Qed.
Hint Rewrite @Second_Id using solve [eauto] : circuitsimpl.

Lemma Compose_Id_l {i o} c : @cequiv i o (Id >==> c) c.
Proof.
  exists (fun (st1 : unit * value (circuit_state c))
       (st2 : value (circuit_state c)) => st1 = (tt, st2)).
  ssplit; [ reflexivity | ]. simplify. ssplit; reflexivity.
Qed.
Hint Rewrite @Compose_Id_l using solve [eauto] : circuitsimpl.

Lemma Compose_Id_r {i o} c : @cequiv i o (c >==> Id) c.
Proof.
  exists (fun (st1 : value (circuit_state c) * unit)
       (st2 : value (circuit_state c)) => st1 = (st2, tt)).
  ssplit; [ reflexivity | ]. simplify. ssplit; reflexivity.
Qed.
Hint Rewrite @Compose_Id_r using solve [eauto] : circuitsimpl.

Lemma Compose_assoc {A B C D}
      (f : Circuit A B) (g : Circuit B C) (h : Circuit C D) :
  cequiv (f >==> (g >==> h)) (f >==> g >==> h).
Proof.
  exists (fun (st1 : value (circuit_state f) * (value (circuit_state g) * value (circuit_state h)))
       (st2 : value (circuit_state f) * value (circuit_state g) * value (circuit_state h)) =>
       st1 = (fst (fst st2), (snd (fst st2), snd st2))).
  ssplit; [ reflexivity | ]. simplify. ssplit; reflexivity.
Qed.
Hint Rewrite @Compose_assoc : circuitsimpl.

Lemma First_Compose {A B C D} (f : Circuit A B) (g : Circuit B C) :
  @cequiv (A * D) (C * D) (First (f >==> g)) (First f >==> First g).
Proof.
  exists eq. ssplit; [ reflexivity | ]. simplify. ssplit; reflexivity.
Qed.
Hint Rewrite @First_Compose using solve [eauto] : circuitsimpl.

Lemma Second_Compose {A B C D} (f : Circuit A B) (g : Circuit B C) :
  @cequiv (D * A) (D * C) (Second (f >==> g)) (Second f >==> Second g).
Proof.
  exists eq. ssplit; [ reflexivity | ]. simplify. ssplit; reflexivity.
Qed.
Hint Rewrite @Second_Compose using solve [eauto] : circuitsimpl.

Lemma LoopInitCE_First_r {A B C} (s : SignalType) reset
      (body : Circuit (A * s) (B * s)) (f : Circuit B C) :
  cequiv (LoopInitCE reset (body >==> First f)) (LoopInitCE reset body >==> f).
Proof.
  exists (fun (st1 : value (circuit_state body) * value (circuit_state f) * combType s)
       (st2 : value (circuit_state body) * combType s * value (circuit_state f)) =>
       st1 = (fst (fst st2), snd st2, snd (fst st2))).
  ssplit; [ reflexivity | ]. simplify. ssplit; reflexivity.
Qed.
Hint Rewrite @LoopInitCE_First_r using solve [eauto] : push_loop.

Lemma LoopInit_First_r {A B C} (s : SignalType) reset
      (body : Circuit (A * s) (B * s)) (f : Circuit B C) :
  cequiv (LoopInit reset (body >==> First f)) (LoopInit reset body >==> f).
Proof.
  cbv [LoopInit]. simpl_ident. rewrite <-Compose_assoc, LoopInitCE_First_r. reflexivity.
Qed.
Hint Rewrite @LoopInit_First_r using solve [eauto] : push_loop.

Lemma LoopCE_First_r {A B C} (s : SignalType)
      (body : Circuit (A * s) (B * s)) (f : Circuit B C) :
  cequiv (LoopCE (body >==> First f)) (LoopCE body >==> f).
Proof. apply LoopInitCE_First_r. Qed.
Hint Rewrite @LoopCE_First_r using solve [eauto] : push_loop.

Lemma Loop_First_r {A B C} (s : SignalType)
      (body : Circuit (A * s) (B * s)) (f : Circuit B C) :
  cequiv (Loop (body >==> First f)) (Loop body >==> f).
Proof. apply LoopInit_First_r. Qed.
Hint Rewrite @Loop_First_r using solve [eauto] : push_loop.

Lemma simulate_Id {t} input : simulate (i:=t) Id input = input.
Proof.
  cbv [Id]; autorewrite with push_simulate.
  apply List.map_id_ext; intros.
  reflexivity.
Qed.
Hint Rewrite @simulate_Id using solve [eauto] : push_simulate.

Lemma simulate_Par {A B C D} c1 c2 input :
  simulate (@Par _ _ A B C D c1 c2) input
  = combine (simulate c1 (map fst input))
            (simulate c2 (map snd input)).
Proof.
  cbv [Par]; autorewrite with push_simulate.
  rewrite map_fst_combine, map_snd_combine by length_hammer.
  reflexivity.
Qed.
Hint Rewrite @simulate_Par using solve [eauto] : push_simulate.

Global Instance Proper_Par {A B C D} :
  Proper (cequiv ==> cequiv ==> cequiv) (@Par _ _ A B C D).
Proof.
  cbv [Par]. repeat intro.
  repeat match goal with H : cequiv _ _ |- _ => rewrite H end.
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
  exists (fun _ _ => True). ssplit; [ tauto | ].
  cbn [value circuit_state]; intros. destruct_products.
  repeat lazymatch goal with x : unit |- _ => destruct x end.
  ssplit; reflexivity.
Qed.
Hint Rewrite @Second_Comb using solve [eauto] : pull_comb.

Lemma First_Comb {i o t} f :
  cequiv (First (Comb f)) (Comb (i:=i*t) (o:=o*t) (fun x => (f (fst x), snd x))).
Proof.
  exists (fun _ _ => True). ssplit; [ tauto | ].
  cbn [value circuit_state]; intros. destruct_products.
  repeat lazymatch goal with x : unit |- _ => destruct x end.
  ssplit; reflexivity.
Qed.
Hint Rewrite @First_Comb using solve [eauto] : pull_comb.

Lemma Compose_Comb {i t o} f g :
  cequiv (@Compose _ _ i t o (Comb f) (Comb g)) (Comb (f >=> g)).
Proof.
  exists (fun _ _ => True). ssplit; [ tauto | ].
  cbn [value circuit_state]; intros. destruct_products.
  repeat lazymatch goal with x : unit |- _ => destruct x end.
  ssplit; reflexivity.
Qed.
Hint Rewrite @Compose_Comb using solve [eauto] : pull_comb.

Lemma Compose_Comb_r {i t1 t2 o} c f g :
  cequiv (@Compose _ _ i t2 o (@Compose _ _ i t1 t2 c (Comb f)) (Comb g))
         (c >==> Comb (f >=> g)).
Proof.
  rewrite <-Compose_Comb. autorewrite with circuitsimpl. reflexivity.
Qed.
Hint Rewrite @Compose_Comb_r using solve [eauto] : pull_comb.

Lemma First_Second_comm {i1 i2 o1 o2} (c1 : Circuit i1 o1) (c2 : Circuit i2 o2) :
  cequiv (First c1 >==> Second c2) (Second c2 >==> First c1).
Proof.
  exists (fun s1 s2 => s1 = (snd s2, fst s2)).
  ssplit; [ reflexivity | ]. cbn [value circuit_state].
  intros; destruct_products. cbn [fst snd] in *.
  logical_simplify. ssplit; reflexivity.
Qed.
Hint Rewrite <- @First_Second_comm using solve [eauto] : circuitsimpl.

Lemma Comb_ext {i o} (f g : value i -> cava (value o)) :
  (forall x, f x = g x) -> cequiv (Comb f) (Comb g).
Proof.
  intro Hfg. exists (fun _ _ => True). ssplit; [ tauto | ].
  cbn [value circuit_state]; intros. destruct_products.
  repeat lazymatch goal with x : unit |- _ => destruct x end.
  cbn [step]. rewrite Hfg.
  ssplit; [ reflexivity | tauto ].
Qed.
